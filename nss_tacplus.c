/*
 * Copyright (C) 2014, 2015, 2016, 2017, 2018, 2019 Cumulus Networks, Inc.
 * All rights reserved.
 * Author: Dave Olson <olson@cumulusnetworks.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program - see the file COPYING.
 */

/*
 * This plugin implements getpwnam_r for NSS over TACACS+
 * and implements getpwuid_r for UIDs if and only if a mapped
 * TACACS+ user is currently logged in (libtacplus_map)
 * This means that if you do, e.g.: ls -ld ~tacacs15, you will
 * sometimes get a mapped username, and other times get tacacs15,
 * depending on whether a mapped user is logged in or not.
 */


#include <string.h>
#include <syslog.h>
#include <stdbool.h>
#include <stdlib.h>
#include <pwd.h>
#include <errno.h>
#include <fcntl.h>
#include <ctype.h>
#include <nss.h>
#include <libaudit.h>
#include <stddef.h>
#include <grp.h>
#include <sys/socket.h>
#include <sys/stat.h>

#include <tacplus/libtac.h>
#include <tacplus/map_tacplus_user.h>

#include "nss_tacplus.h"

static const char *nssname = "nss_tacplus"; /* for syslogs */
static const char *config_file = "/etc/tacplus_nss.conf";

/*
 * pwbuf is used to reduce number of arguments passed around; the strings in
 * the passwd struct need to point into this buffer.
 */
struct pwbuf {
    char *name;
    char *buf;
    struct passwd *pw;
    int *errnop;
    size_t buflen;
};

typedef struct {
    struct addrinfo *addr;
    char *key;
    unsigned not_resp;
} tacplus_server_t;

/* set from configuration file parsing */
static tacplus_server_t tac_srv[TAC_PLUS_MAXSERVERS];
static int tac_srv_no, tac_key_no;
static char tac_service[] = "shell";
static char tac_protocol[] = "ssh";
static char tac_rhost[INET6_ADDRSTRLEN];
static char vrfname[64];
static char *exclude_users;
static uid_t min_uid = ~0U; /*  largest possible */
static int debug;
static int printed_srvs;
static uint16_t use_tachome;
static int conf_parsed = 0;
static struct sockaddr src_sockaddr;
static struct addrinfo src_addr_info;
static struct addrinfo *src_addr;

static void get_remote_addr(void);

#define MAX_INCL 8 /*  max config level nesting */

/*  reset all config variables when we are going to re-parse */
static void
reset_config(void)
{
    int i, nservers;

    /*  reset the config variables that we use, freeing memory where needed */
    nservers = tac_srv_no;
    tac_srv_no = 0;
    tac_key_no = 0;
    vrfname[0] = '\0';
    if(exclude_users) {
        (void)free(exclude_users);
        exclude_users = NULL;
    }
    debug = 0;
    printed_srvs = 0;
    use_tachome = 0;
    tac_timeout = 0;
    min_uid = ~0U;
    src_addr = NULL;

    for(i = 0; i < nservers; i++) {
        if(tac_srv[i].key) {
            free(tac_srv[i].key);
            tac_srv[i].key = NULL;
        }
        tac_srv[i].addr = NULL;
        tac_srv[i].not_resp = 0;
    }
}

/* Convert ip address string to address info.
 * It returns 0 on success, or -1 otherwise
 * It supports ipv4 only.
 */
static int str_to_ipv4(const char *srcaddr, struct addrinfo *p_addr_info)
{
    struct sockaddr_in *s_in;

    s_in = (struct sockaddr_in *)p_addr_info->ai_addr;
    s_in->sin_family = AF_INET;
    s_in->sin_addr.s_addr = INADDR_ANY;

    if (inet_pton(AF_INET, srcaddr, &(s_in->sin_addr)) == 1) {
        p_addr_info->ai_family = AF_INET;
        p_addr_info->ai_addrlen = sizeof (struct sockaddr_in);
        return 0;
    }
    return -1;
}

static int nss_tacplus_config(int *errnop, const char *cfile, int top)
{
    FILE *conf;
    char lbuf[2048];
    static struct stat lastconf[MAX_INCL];
    static char *cfilelist[MAX_INCL];
    struct stat st, *lst;

    if(top > MAX_INCL) {
        syslog(LOG_NOTICE, "%s: Config file include depth > %d, ignoring %s",
            nssname, MAX_INCL, cfile);
        return 1;
    }

    lst = &lastconf[top-1];
    if(conf_parsed && top == 1) {
        /*
         *  check to see if the config file(s) have changed since last time,
         *  in case we are part of a long-lived daemon.  If any changed,
         *  reparse.  If not, return the appropriate status (err or OK)
         *  This is somewhat complicated by the include file mechanism.
         *  When we have nested includes, we have to check all the config
         *  files we saw previously, not just the top level config file.
         */
        int i;
        for(i=0; i < MAX_INCL; i++) {
            struct stat *cst;
            cst = &lastconf[i];
            if(!cst->st_ino || !cfilelist[i]) /* end of files */
                return conf_parsed == 2 ? 0 : 1;
            if (stat(cfilelist[i], &st) || st.st_ino != cst->st_ino ||
                st.st_mtime !=  cst->st_mtime || st.st_ctime != cst->st_ctime)
                break; /* found removed or different file, so re-parse */
        }
        reset_config();
        syslog(LOG_NOTICE, "%s: Configuration file(s) have changed, "
               "re-initializing", nssname);
    }

    /*  don't check for failures, we'll just skip, don't want to error out */
    cfilelist[top-1] = strdup(cfile);
    conf = fopen(cfile, "r");
    if(conf == NULL) {
        *errnop = errno;
        if(!conf_parsed && debug) /*  debug because privileges may not allow */
            syslog(LOG_DEBUG, "%s: can't open config file %s: %m",
                nssname, cfile);
        return 1;
    }
    if (fstat(fileno(conf), lst) != 0)
        memset(lst, 0, sizeof *lst); /*  avoid stale data, no warning */

    while(fgets(lbuf, sizeof lbuf, conf)) {
        if(*lbuf == '#' || isspace(*lbuf))
            continue; /* skip comments, white space lines, etc. */
        strtok(lbuf, " \t\n\r\f"); /* terminate buffer at first whitespace */
        if(!strncmp(lbuf, "include=", 8)) {
            /*
             * allow include files, useful for centralizing tacacs
             * server IP address and secret.  When running non-privileged,
             * may not be able to read one or more config files.
             */
            if(lbuf[8])
                (void)nss_tacplus_config(errnop, &lbuf[8], top+1);
        }
        else if(!strncmp(lbuf, "debug=", 6))
            debug = strtoul(lbuf+6, NULL, 0);
        else if (!strncmp (lbuf, "user_homedir=", 13))
            use_tachome = (uint16_t)strtoul(lbuf+13, NULL, 0);
        else if (!strncmp (lbuf, "timeout=", 8)) {
            char *argend;
            int val = (unsigned)strtol(lbuf+8, &argend, 0);
            if (argend != (lbuf+8) && val >= 0) {
                tac_timeout = val;
                tac_readtimeout_enable = 1;
            }
            else
                syslog(LOG_WARNING, "%s: invalid parameter value (%s)",
                    nssname, lbuf);
        }
        /*
         * This next group is here to prevent a warning in the
         * final "else" case.  We don't need them, but if there
         * is a common included file, we might see them.
         */
        else if(!strncmp(lbuf, "service=", 8) ||
            !strncmp(lbuf, "protocol=", 9) ||
            !strncmp(lbuf, "login=", 6))
            ;
        else if(!strncmp(lbuf, "secret=", 7)) {
            int i;
            /* no need to complain if too many on this one */
            if(tac_key_no < TAC_PLUS_MAXSERVERS) {
                if((tac_srv[tac_key_no].key = strdup(lbuf+7)))
                    tac_key_no++;
                else
                    /* don't log the actual line, it's a security issue */
                    syslog(LOG_ERR, "%s: unable to copy server secret %d: %m",
                        nssname, tac_key_no);
            }
            /* handle case where 'secret=' was given after a 'server='
             * parameter, fill in the current secret */
            for(i = tac_srv_no-1; i >= 0; i--) {
                if (tac_srv[i].key)
                    continue;
                tac_srv[i].key = strdup(lbuf+7);
            }
        }
        else if (!strncmp (lbuf, "source_ip=", 10)) {
            const char *srcip = lbuf + 10;
            /* if source ip address, convert it to addr info  */
            memset (&src_addr_info, 0, sizeof (struct addrinfo));
            memset (&src_sockaddr, 0, sizeof (struct sockaddr));
            src_addr_info.ai_addr = &src_sockaddr;
            if (str_to_ipv4 (srcip, &src_addr_info) == 0)
                src_addr = &src_addr_info;
            else {
                src_addr = NULL; /* for re-parsing or errors */
                syslog(LOG_WARNING,
                       "%s: unable to convert %s to an IPv4 address", nssname,
                       lbuf);
            }
        }
        else if(!strncmp(lbuf, "exclude_users=", 14)) {
            /*
             * Don't lookup users in this comma-separated list for both
             * robustness and performnce.  Typically root and other commonly
             * used local users.  If set, we also look up the uids
             * locally, and won't do remote lookup on those uids either.
             */
            exclude_users = strdup(lbuf+14);
        }
        else if(!strncmp(lbuf, "min_uid=", 8)) {
            /*
             * Don't lookup uids that are local, typically set to either
             * 0 or smallest always local user's uid
             */
            unsigned long uid;
            char *valid;
            uid = strtoul(lbuf+8, &valid, 0);
            if (valid > (lbuf+8))
                min_uid = (uid_t)uid;
        }
        else if(!strncmp(lbuf, "vrf=", 4))
            strncpy(vrfname, lbuf + 4, sizeof(vrfname));
        else if(!strncmp(lbuf, "server=", 7)) {
            if(tac_srv_no < TAC_PLUS_MAXSERVERS) {
                struct addrinfo hints, *servers, *server;
                int rv;
                char *port, server_buf[sizeof lbuf];

                memset(&hints, 0, sizeof hints);
                hints.ai_family = AF_UNSPEC;  /* use IPv4 or IPv6, whichever */
                hints.ai_socktype = SOCK_STREAM;

                strcpy(server_buf, lbuf + 7);

                port = strchr(server_buf, ':');
                if(port != NULL) {
                    *port = '\0';
                    port++;
                }
                if((rv = getaddrinfo(server_buf, (port == NULL) ?
                            "49" : port, &hints, &servers)) == 0) {
                    for(server = servers; server != NULL &&
                        tac_srv_no < TAC_PLUS_MAXSERVERS;
                        server = server->ai_next) {
                        tac_srv[tac_srv_no].addr = server;
                        /* use current key, if our index not yet set */
                        if(tac_key_no && !tac_srv[tac_srv_no].key)
                            tac_srv[tac_srv_no].key =
                                strdup(tac_srv[tac_key_no-1].key);
                        tac_srv_no++;
                    }
                }
                else {
                    syslog(LOG_ERR,
                        "%s: skip invalid server: %s (getaddrinfo: %s)",
                        nssname, server_buf, gai_strerror(rv));
                }
            }
            else {
                syslog(LOG_WARNING, "%s: maximum number of servers (%d) "
                    "exceeded, skipping", nssname, TAC_PLUS_MAXSERVERS);
            }
        }
        else if(debug) /* ignore unrecognized lines, unless debug on */
            /*  Don't complain about acct_all, may be set in shared
             *  config, even if we don't use it.
             */
            if(strncmp(lbuf, "acct_all=", 9))
                syslog(LOG_WARNING, "%s: unrecognized parameter: %s",
                    nssname, lbuf);
    }
    fclose(conf);


    return 0;
}

/* common get config code at each entry point */
static int
get_config(int *errp, int level)
{
    int result = nss_tacplus_config(errp, config_file, 1);
    conf_parsed = result == 0 ? 2 : 1;

    get_remote_addr();

    /* no config file, no servers, etc.
     * this is a debug because privileges may not allow access
     * for included files.
    */
    if(debug && result)
        syslog(LOG_DEBUG, "%s: bad config or server line for nss_tacplus",
            nssname);
    return result;
}


/*
 * Separate function so we can print first time we try to connect,
 * rather than during config.
 * Don't print at config, because often the uid lookup is one we
 * skip due to min_uid, so no reason to clutter the log.
 */
static void print_servers(void)
{
    int n;

    if (printed_srvs || !debug)
        return;
    printed_srvs = 1;

    if(tac_srv_no == 0)
        syslog(LOG_DEBUG, "%s:%s: no TACACS %s in config (or no permission),"
            " giving up",
            nssname, __FUNCTION__, tac_srv_no ? "service" :
            (*tac_service ? "server" : "service and no server"));

    /*  do not log tac_srv[n].key; it's a security issue */
    for(n = 0; n < tac_srv_no; n++)
        syslog(LOG_DEBUG, "%s: server[%d] { addr=%s }", nssname,
            n, tac_srv[n].addr ? tac_ntop(tac_srv[n].addr->ai_addr)
            : "unknown");
}

/*
 * copy a passwd structure and it's strings, using the provided buffer
 * for the strings.
 * if usename is non-NULL, use that, rather than pw_name in srcpw, so we can
 * preserve the original requested name (this is part of the tacacs remapping).
 * For strings, if pointer is null, use an empty string.
 * Returns 0 if everything fit, otherwise 1.
 */
static int
pwcopy(char *buf, size_t len, struct passwd *srcpw, struct passwd *destpw,
       const char *usename, uint16_t tachome)
{
    int needlen, cnt, origlen = len;
    char *shell;

    if(!usename) {
        usename = srcpw->pw_name;
        tachome = 0; /*  early lookups; no tachome */
    }

    needlen = usename ? strlen(usename) + 1 : 1 +
        srcpw->pw_dir ? strlen(srcpw->pw_dir) + 1 : 1 +
        srcpw->pw_gecos ? strlen(srcpw->pw_gecos) + 1 : 1 +
        srcpw->pw_shell ? strlen(srcpw->pw_shell) + 1 : 1 +
        srcpw->pw_passwd ? strlen(srcpw->pw_passwd) + 1 : 1;
    if(needlen > len) {
        if(debug)
            syslog(LOG_DEBUG, "%s provided password buffer too small (%ld<%d)",
                nssname, (long)len, needlen);
        return 1;
    }

    destpw->pw_uid = srcpw->pw_uid;
    destpw->pw_gid = srcpw->pw_gid;

    cnt = snprintf(buf, len, "%s", usename ? usename : "");
    destpw->pw_name = buf;
    cnt++; /* allow for null byte also */
    buf += cnt;
    len -= cnt;
    cnt = snprintf(buf, len, "%s", srcpw->pw_passwd ? srcpw->pw_passwd : "");
    destpw->pw_passwd = buf;
    cnt++;
    buf += cnt;
    len -= cnt;
    cnt = snprintf(buf, len, "%s", srcpw->pw_shell ? srcpw->pw_shell : "");
    destpw->pw_shell = buf;
    shell = strrchr(buf, '/');
    shell = shell ? shell+1 : buf;
    if (tachome && *shell == 'r') {
        tachome = 0;
        if(debug > 1)
            syslog(LOG_DEBUG, "%s tacacs login %s with user_homedir not allowed"
                "; shell is %s", nssname, srcpw->pw_name, buf);
    }
    cnt++;
    buf += cnt;
    len -= cnt;
    cnt = snprintf(buf, len, "%s", srcpw->pw_gecos ? srcpw->pw_gecos : "");
    destpw->pw_gecos = buf;
    cnt++;
    buf += cnt;
    len -= cnt;
    if (tachome && usename) {
        char *slash, dbuf[strlen(srcpw->pw_dir) + strlen(usename)];
        snprintf(dbuf, sizeof dbuf, "%s", srcpw->pw_dir ? srcpw->pw_dir : "");
        slash = strrchr(dbuf, '/');
        if (slash) {
            slash++;
            snprintf(slash, sizeof dbuf - (slash-dbuf), "%s", usename);
        }
        cnt = snprintf(buf, len, "%s", dbuf);
    }
    else
        cnt = snprintf(buf, len, "%s", srcpw->pw_dir ? srcpw->pw_dir : "");
    destpw->pw_dir = buf;
    cnt++;
    len -= cnt;
    if(len < 0) {
        if(debug)
            syslog(LOG_DEBUG, "%s provided password buffer too small (%ld<%d)",
                nssname, (long)origlen, origlen-(int)len);
        return 1;
    }

    return 0;
}

/*
 * Find the username or the matching tacacs privilege user in /etc/passwd
 * We use fgetpwent() so we can check the local file, always.
 * This could cause problems if somebody is using local users, ldap, and tacacs,
 * but we just require that the mapped user always be a local user.  Since the
 * local user password isn't supposed to be used, that should be OK.
 *
 * We shouldn't normally find the username, because tacacs lookup should be
 * configured to follow local in nsswitch.conf, but somebody may configure the
 * other way, so we look for both the given user, and our "matching" user name
 * based on the tacacs authorization level.
 *
 * If not found, then try to map to a localuser tacacsN where N <= to the
 * TACACS+ privilege level, using the APIs in libtacplus_map.so
 * algorithm in update_mapuser(), but only considering tacacs users.
 * Returns 0 on success, else 1
 */
static int
find_pw_userpriv(unsigned priv, struct pwbuf *pb)
{
    FILE *pwfile;
    struct passwd tpw, *ent;
    int matches, ret, rett;
    unsigned origpriv = priv;
    char tbuf[pb->buflen];
    char tacuser[9]; /* "tacacs" followed by 1-2 digits */

    tacuser[0] = '\0';

    pwfile = fopen("/etc/passwd", "r");
    if(!pwfile) {
        syslog(LOG_WARNING, "%s: failed to open /etc/passwd: %m", nssname);
        return 1;
    }

recheck:
    snprintf(tacuser, sizeof tacuser, "tacacs%u", priv);
    tpw.pw_name = NULL;
    rett = 0;
    for(matches=0; !matches && (ent = fgetpwent(pwfile)); ) {
        if(ent->pw_name && !strcmp(ent->pw_name, tacuser)) {
            rett = pwcopy(tbuf, sizeof(tbuf), ent, &tpw, NULL, use_tachome);
            matches++;
        }
    }
    if(!matches && priv > 0) {
        priv--;
        rewind(pwfile);
        goto recheck;
    }
    ret = 1;
    fclose(pwfile);
    if(matches)  {
        if(priv != origpriv && debug)
            syslog(LOG_DEBUG, "%s: local user not found at privilege=%u,"
                " using %s", nssname, origpriv, tacuser);
        if(tpw.pw_name && !rett) {
            ret = pwcopy(pb->buf, pb->buflen, &tpw, pb->pw, pb->name,
                use_tachome);
        }
    }
    if(ret)
       *pb->errnop = ERANGE;

    return ret;
}

/*
 * This is similar to find_pw_userpriv(), but passes in a fixed
 * name for UID lookups, where we have the mapped name from the
 * map file, so trying multiple tacacsN users would be wrong.
 * Some commonality, but ugly to factor
 * Only applies to mapped users
 * returns 0 on success
 */
static int
find_pw_user(const char *logname, const char *tacuser, struct pwbuf *pb,
    uint16_t usetachome)
{
    FILE *pwfile;
    struct passwd *ent;
    int ret = 1;

    if(!tacuser) {
        if(debug)
            syslog(LOG_DEBUG, "%s: passed null username, failing", nssname);
        return 1;
    }

    pwfile = fopen("/etc/passwd", "r");
    if(!pwfile) {
        syslog(LOG_WARNING, "%s: failed to open /etc/passwd: %m",
            nssname);
        return 1;
    }

    pb->pw->pw_name = NULL; /* be paranoid */
    for(ret = 1; ret && (ent = fgetpwent(pwfile)); ) {
        if(!ent->pw_name)
            continue; /* shouldn't happen */
        if(!strcmp(ent->pw_name, tacuser)) {
            ret = pwcopy(pb->buf, pb->buflen, ent, pb->pw, logname, usetachome);
            break;
        }
    }
    fclose(pwfile);
    if(ret)
       *pb->errnop = ERANGE;

    return ret;
}

/*
 * we got the user back.  Go through the attributes, find their privilege
 * level, map to the local user, fill in the data, etc.
 * Returns 0 on success, 1 on errors.
 */
static int
got_tacacs_user(struct tac_attrib *attr, struct pwbuf *pb)
{
    unsigned long priv_level = 0;

    while(attr != NULL)  {
        /* we are looking for the privilege attribute, can be in several forms,
         * typically priv-lvl= or priv_lvl= */
        if(strncasecmp(attr->attr, "priv", 4) == 0) {
            char *ok, *val;

            for(val=attr->attr; *val && *val != '*' && *val != '='; val++)
                ;
            if(!*val)
                continue;
            val++;

            priv_level = strtoul(val, &ok, 0);

            /* if this fails, we leave priv_level at 0, which is
             * least privileged, so that's OK, but at least report it
             */
            if(ok == val && debug)
                syslog(LOG_WARNING, "%s: non-numeric privilege for %s, (%s)",
                    nssname, pb->name, attr->attr);
        }
        attr = attr->next;
    }

    return find_pw_userpriv(priv_level, pb);
}

/*
 * Attempt to connect to the requested tacacs server.
 * Returns fd for connection, or -1 on failure
 */

static int
connect_tacacs(struct tac_attrib **attr, int srvr)
{
    int fd;

    fd = tac_connect_single(tac_srv[srvr].addr, tac_srv[srvr].key, src_addr,
        vrfname[0]?vrfname:NULL);
    if(fd >= 0) {
        tac_add_attrib(attr, "service", tac_service);
        if(tac_protocol[0])
            tac_add_attrib(attr, "protocol", tac_protocol);
        /* empty cmd is required, at least for linux tac_plus */
        tac_add_attrib(attr, "cmd", "");
    }
    return fd;
}

/*
 * If all servers have been unresponsive, clear that state, so we try
 * them all.  It might have been transient.
 */
static void tac_chk_anyresp(void)
{
    int i, anyok=0;

    for(i = 0; i < tac_srv_no; i++) {
        if (!tac_srv[i].not_resp)
            anyok++;
    }
    if (!anyok) {
        for(i = 0; i < tac_srv_no; i++)
            tac_srv[i].not_resp = 0;
    }
}



/*
 * lookup the user on a TACACS server.  Returns 0 on successful lookup, else 1
 *
 * Make a new connection each time, because libtac is single threaded and
 * doesn't support multiple connects at the same time due to use of globals,
 * and doesn't have support for persistent connections.   That's fixable, but
 * not worth the effort at this point.
 * Step through all servers until success or end of list, because different
 * servers can have different databases.
 */
static int
lookup_tacacs_user(struct pwbuf *pb)
{
    struct areply arep;
    int ret = 1, done = 0;
    struct tac_attrib *attr = NULL;
    int tac_fd, srvr;

    if (exclude_users) {
        char *user, *list;
        list = strdup(exclude_users);
        if (list) {
            static const char *delim = ", \t\n";
            bool islocal = 0;
            user = strtok(list, delim);
            list = NULL;
            while (user) {
                if(!strcmp(user, pb->name)) {
                    islocal = 1;
                    break;
                }
                user = strtok(NULL, delim);
            }
            free(list);
            if (islocal)
                return 2;
        }
    }

    if(!*tac_service) /* reported at config file processing */
        return ret;
    print_servers();

    tac_chk_anyresp();
    for(srvr=0; srvr < tac_srv_no && !done; srvr++) {
        if (tac_srv[srvr].not_resp)
            continue; /*  don't retry if previously not responding */
        arep.msg = NULL;
        arep.attr = NULL;
        arep.status = TAC_PLUS_AUTHOR_STATUS_ERROR; /* if author_send fails */
        tac_fd = connect_tacacs(&attr, srvr);
        if (tac_fd < 0) {
            tac_srv[srvr].not_resp = 1;
            if(debug)
                syslog(LOG_WARNING, "%s: failed to connect TACACS+ server %s,"
                    " ret=%d: %m", nssname, tac_srv[srvr].addr ?
                    tac_ntop(tac_srv[srvr].addr->ai_addr) : "unknown", tac_fd);
            tac_free_attrib(&attr);
            continue;
        }
        ret = tac_author_send(tac_fd, pb->name, "", tac_rhost, attr);
        if(ret < 0) {
            if(debug)
                syslog(LOG_WARNING, "%s: TACACS+ server %s authorization "
                       "failed (%d) user (%s)", nssname, tac_srv[srvr].addr ?
                       tac_ntop(tac_srv[srvr].addr->ai_addr) : "unknown", ret,
                       pb->name);
        }
        else  {
            errno = 0;
            ret = tac_author_read(tac_fd, &arep);
            if (ret == LIBTAC_STATUS_PROTOCOL_ERR)
                syslog(LOG_WARNING, "%s: TACACS+ server %s read failed with"
                    " protocol error (incorrect shared secret?) user %s",
                    nssname, tac_ntop(tac_srv[srvr].addr->ai_addr), pb->name);
            else if (ret < 0) /*  ret == 1 OK transaction, use arep.status */
                syslog(LOG_WARNING, "%s: TACACS+ server %s read failed (%d) for"
                    " user %s: %m", nssname,
                    tac_ntop(tac_srv[srvr].addr->ai_addr), ret, pb->name);
        }

        tac_free_attrib(&attr);
        close(tac_fd);
        if(ret < 0)
            continue;

        if(arep.status == AUTHOR_STATUS_PASS_ADD ||
           arep.status == AUTHOR_STATUS_PASS_REPL) {
            ret = got_tacacs_user(arep.attr, pb);
            if(debug>1)
                syslog(LOG_DEBUG, "%s: TACACS+ server %s successful for user %s"
                    " local lookup %s", nssname,
                    tac_ntop(tac_srv[srvr].addr->ai_addr), pb->name,
                    ret?"copy problem":"OK");
            else if(debug)
                syslog(LOG_DEBUG, "%s: TACACS+ server %s success on user %s",
                    nssname, tac_ntop(tac_srv[srvr].addr->ai_addr), pb->name);
            done = 1; /* break out of loop after arep cleanup */
        }
        else {
            ret = 1; /*  in case last server */
            if(debug)
                syslog(LOG_DEBUG, "%s: TACACS+ server %s replies user %s"
                    " invalid (%d)", nssname,
                    tac_ntop(tac_srv[srvr].addr->ai_addr), pb->name,
                    arep.status);
        }
        if(arep.msg)
            free(arep.msg);
        if(arep.attr) /* free returned attributes */
            tac_free_attrib(&arep.attr);
    }

    return ret < 0? 1 : ret;
}

static int
lookup_mapped_uid(struct pwbuf *pb, uid_t uid, uid_t auid, int session)
{
    char *loginname, mappedname[256];
    uint16_t flag;
    int ret = 1;

    mappedname[0] = '\0';
    loginname = lookup_mapuid(uid, auid, session,
                            mappedname, sizeof mappedname, &flag);
    if(loginname) {
        ret = find_pw_user(loginname, mappedname, pb, flag & MAP_USERHOMEDIR);
        free(loginname);
    }
    return ret;
}

/*
 * This is an NSS entry point.
 * We implement getpwnam(), because we remap from the tacacs login
 * to the local tacacs0 ... tacacs15 users for all other info, and so
 * the normal order of "passwd tacplus" (possibly with ldap or anything
 * else prior to tacplus) will mean we only get used when there isn't
 * a local user to be found.
 *
 * We try the lookup to the tacacs server first.  If we can't make a
 * connection to the server for some reason, we also try looking up
 * the account name via the mapping file, primarily to handle cases
 * where we aren't running with privileges to read the tacacs configuration
 * (since it has the secret key).
 */
enum nss_status _nss_tacplus_getpwnam_r(const char *name, struct passwd *pw,
    char *buffer, size_t buflen, int *errnop)
{
    enum nss_status status = NSS_STATUS_NOTFOUND;
    int result, lookup;
    struct pwbuf pbuf;

    result = get_config(errnop, 1);
    if(result)
        return status;

    /* marshal the args for the lower level functions */
    pbuf.name = (char *)name;
    pbuf.pw = pw;
    pbuf.buf = buffer;
    pbuf.buflen = buflen;
    pbuf.errnop = errnop;

    lookup = lookup_tacacs_user(&pbuf);
    if(!lookup) {
        status = NSS_STATUS_SUCCESS;
        if (errnop)
            *errnop = 0;
    }
    else if(lookup == 1) { /*  2 means exclude_users match */
        uint16_t flag;
        /*
         * If we can't contact a tacacs server (either not configured, or
         * more likely, we aren't running as root and the config for the
         * server is not readable by our uid for security reasons), see if
         * we can find the user via the mapping database, and if so, use
         * that.  This will work for non-root users as long as the requested
         * name is in use (that is, logged in), which will be the most
         * common case of wanting to use the original login name by non-root
         * users.
         */
        char *mapname = lookup_mapname(name, -1, -1, NULL, &flag);
        if(mapname != name && !find_pw_user(name, mapname, &pbuf,
                flag & MAP_USERHOMEDIR))
            status = NSS_STATUS_SUCCESS;
    }

    if (status == NSS_STATUS_SUCCESS && errnop)
        *errnop = 0; /*  be sane, no stale errno */

   return status;
}

/*
 * This is an NSS entry point.
 * We implement getpwuid(), for anything that wants to get the original
 * login name from the uid.
 * If it matches an entry in the map, we use that data to replace
 * the data from the local passwd file (not via NSS).
 * locally from the map.
 *
 * This can be made to work 2 different ways, and we need to choose
 * one, or make it configurable.
 *
 * 1) Given a valid auid and a session id, and a mapped user logged in,
 * we'll match only that user.   That is, we can only do the lookup
 * successfully for child processes of the mapped tacacs login, and
 * only while still logged in (map entry is valid).
 *
 * 2) Use auid/session wildcards, and and always match on the first valid
 * tacacs map file entry.  This means if two tacacs users are logged in
 * at the same privilege level at the same time, uid lookups for ps, ls,
 * etc. will return the first (in the map file, not necessarily first
 * logged in) mapped name.
 *
 * For now, if auid and session are set, I try them, and if that lookup
 * fails, try the wildcard.
 *
 * Only works while the UID is in use for a mapped user, and only
 * for processes invoked from that session.  Other callers will
 * just get the files, ldap, or nis entry for the UID
 * Only works while the UID is in use for a mapped user, and returns
 * the first match from the mapped users.
 */
enum nss_status _nss_tacplus_getpwuid_r(uid_t uid, struct passwd *pw,
    char *buffer, size_t buflen, int *errnop)
{
    struct pwbuf pb;
    enum nss_status status = NSS_STATUS_NOTFOUND;
    int session;
    uid_t auid;

    (void) get_config(errnop, 1);
    /*  config errors aren't fatal here */
    if (min_uid != ~0U && uid < min_uid) {
        if(debug > 1)
            syslog(LOG_DEBUG, "%s: uid %u < min_uid %u, don't lookup",
                nssname, uid, min_uid);
        return status;
    }

    auid = audit_getloginuid(); /* audit_setloginuid not called */
    session = map_get_sessionid();

    /* marshal the args for the lower level functions */
    pb.pw = pw;
    pb.buf = buffer;
    pb.buflen = buflen;
    pb.errnop = errnop;
    pb.name = NULL;

    /*
     * the else case will only be called if we don't have an auid or valid
     * sessionid, since otherwise the first call will be using wildcards,
     * since the getloginuid and get_sessionid calls will "fail".
     */
    if(!lookup_mapped_uid(&pb, uid, auid, session))
        status = NSS_STATUS_SUCCESS;
    else if((auid != (uid_t)-1 || session != ~0U) &&
        !lookup_mapped_uid(&pb, uid, (uid_t)-1, ~0))
        status = NSS_STATUS_SUCCESS;
    return status;
}

static void get_remote_addr(void)
{
    struct sockaddr_storage addr;
    socklen_t len = sizeof addr;
    char ipstr[INET6_ADDRSTRLEN];

    /*  This is so we can fill in the rhost field when we talk to the
     *  TACACS+ server, when it's an ssh connection, so sites that refuse
     *  authorization unless from specific IP addresses will get that
     *  information.  It's pretty much of a hack, but it works.
     */
    if (getpeername(0, (struct sockaddr*)&addr, &len) == -1)
        return;

    *ipstr = 0;
    if (addr.ss_family == AF_INET) {
        struct sockaddr_in *s = (struct sockaddr_in *)&addr;
        inet_ntop(AF_INET, &s->sin_addr, ipstr, sizeof ipstr);
    } else {
        struct sockaddr_in6 *s = (struct sockaddr_in6 *)&addr;
        inet_ntop(AF_INET6, &s->sin6_addr, ipstr, sizeof ipstr);
    }

    snprintf(tac_rhost, sizeof tac_rhost, "%s", ipstr);
    if(debug > 1 && tac_rhost[0])
        syslog(LOG_DEBUG, "%s: rhost=%s", nssname, tac_rhost);
}

/* start of infrastructure for getgr* routines */

static int copyuser(char **grmem, const char *user, long long *blen,
                    int *err)
{
    size_t l = strlen(user) + 1;
    *blen -= l;
    if (*blen < 0) {
        *err = ERANGE;
        return 1;
    }
    strcpy(*grmem, user);
    *grmem += l;
    return 0;
}

/*
* Return a char ** list of strings of usernames from the mapping db
* that for each username such as tacacs15, looks up that name and
* replaces it with usernames logged in and mapped to that name,
* for replacing the gr_mem field for getgrent(), etc.
* Passed the original gr_mem array straight from the group file.
* All strings go into buf, and we return ERANGE in *err if there
* isn't enough room.
* The allocated memory will leak, but it's re-used on each call, so
* not too signficant, and if endgrent() gets called, we'll clean up.
*/
static char **
fixup_gr_mem(const char *grnam, const char **gr_in, char *buf,
             size_t *lenp, int *err)
{
    int nadded = 0, midx = 0;
    long long l = 0, len = *lenp;   /* size_t unsigned on some systems */
    const char **in;
    char **out = NULL, *mem = buf;
    char **gr_mem;
    const unsigned align = sizeof(void *) - 1;

    *err = 0;

    /* set up to copy to supplied buffer */
    l = (((ptrdiff_t)mem + align) & align);
    len -= align;
    mem += align;
    gr_mem = (char **)mem;

    if (!gr_in)
        goto done;

    /* sort of ugly to have to do this twice, to reserve enough
     * space in gr_mem, but it's not too expensive, no connects
     * to a tacacs server.
    */
    for (in=gr_in; in && *in; in++) {
        char *mapnames = lookup_all_mapped(*in);
        if (mapnames) { /*  comma separated list was returned  */
            char *saved, *tok;
            tok = strtok_r(mapnames, ",", &saved);
            while (tok) {
                nadded++;
                tok = strtok_r(NULL, ",", &saved);
            }
        }
        else
            nadded++;
    }
    l = sizeof *gr_mem * (nadded+1);
    len -= l;
    mem += l;

    /*  do the copying in this loop */
    for (in=gr_in; in && *in; in++) {
        char *mapnames = lookup_all_mapped(*in);
        if (mapnames) { /*  comma separated list was returned  */
            char *saved, *tok;
            tok = strtok_r(mapnames, ",", &saved);
            while (tok) {
                gr_mem[midx] = mem;
                if(copyuser(&mem, tok, &len, err))
                    goto done;
                midx++;
                tok = strtok_r(NULL, ",", &saved);
            }
        }
        else { /*  just copy what was returned to the buffer */
            gr_mem[midx] = mem;
            if(copyuser(&mem, *in, &len, err))
                goto done;
            midx++;
        }
    }

 done:
    gr_mem[midx] = NULL;        /*  terminate the list */

    if (*err) {
        syslog(LOG_WARNING, "%s: group %s members truncated due to short"
               " buffer %lld characters", nssname, grnam, (long long)*lenp);
        *lenp = 0;
    } else {
        out = gr_mem;
        *lenp = mem - buf;
    }
    return out;
}

/* end of infrastructure for getgr* routines */
/*
* The group routines are here so we can substitute mappings for radius_user
* and radius_priv_user when reading /etc/group, so that we can make
* users members of the appropriate groups for various privileged
* (and unprivileged) tasks.
* Ideally, we'd be able to use the getgr* routines specifying compat,
* but the NSS plugin infrastructure doesn't support that, so we have to
* read /etc/group directly, and then do our substitutions.
*
* This won't work if the RADIUS users are in LDAP group and/or password
* files, but that's the way it goes.
*
* For the intended purpose, it works well enough.
*
* We need getgrent() for this one, because initgroups needs it, unlike
* the password file.
*/

static FILE *grent;

__attribute__((visibility("default")))
enum nss_status _nss_tacplus_setgrent(void)
{
    enum nss_status status = NSS_STATUS_NOTFOUND;
    static const char *grpname = "/etc/group";
    int error, errval;

    error = get_config(&errval, 1);
    if(error)
        return errval == ENOENT ? NSS_STATUS_UNAVAIL : status;

    if (grent) {
        rewind(grent);
        status = NSS_STATUS_SUCCESS;
        goto done;
    }

    grent = fopen(grpname, "r");
    if (!grent) {
        syslog(LOG_WARNING, "%s: failed to open %s: %m", nssname, grpname);
        status = NSS_STATUS_UNAVAIL;
    } else {
        status = NSS_STATUS_SUCCESS;
        /*  don't leave fd open across execs */
        (void)fcntl(fileno(grent), F_SETFD, FD_CLOEXEC);
    }
 done:
    return status;
}

__attribute__((visibility("default")))
enum nss_status _nss_tacplus_endgrent(void)
{
    if (grent) {
        FILE *f = grent;
        grent = NULL;
        (void)fclose(f);
    }
    return NSS_STATUS_SUCCESS;
}

/*
* do the fixups and copies, using the passed in buffer.  result must
* have been checked to be sure it's non-NULL before calling.
*/
static int fixup_grent(struct group *entry, struct group *result, char *buf,
                       size_t lenbuf, int *errp)
{
    char **grusr, **new_grmem = NULL;
    struct group *newg;
    long long l, len;           /* size_t unsigned on some systems */
    int err, members, memlen;
    int ret = NSS_STATUS_NOTFOUND;
    char *nm = entry->gr_name ? entry->gr_name : "(nil)";
    size_t usedbuf;

    if (!result)                /* should always be non-NULL, just cautious */
        return ret;

    len = lenbuf;
    if (!errp)                  /*  to reduce checks below */
        errp = &err;
    *errp = 0;

    newg = (struct group *)buf;
    len -= sizeof *newg;
    buf += sizeof *newg;
    if (len < 0) {
        *errp = ENOMEM;
        return ret;
    }
    newg->gr_gid = entry->gr_gid;
    l = snprintf(buf, len, "%s", entry->gr_name);
    newg->gr_name = buf;
    len -= l + 1;
    buf += l + 1;
    if (len > 0) {
        l = snprintf(buf, len, "%s", entry->gr_passwd);
        newg->gr_passwd = buf;
        len -= l + 1;
        buf += l + 1;
    }
    if (len < 0) {
        *errp = ENOMEM;
        return NSS_STATUS_TRYAGAIN;
    }

    /*
     * for each member in the group, see if it's a tacacs mapped name, and if
     * so, replace it with the login name(s) mapped to it, if any, otherwise
     * leave it as is.
     */
    for (memlen=members=0, grusr=entry->gr_mem; grusr && *grusr; grusr++) {
        members++;
        memlen += strlen(*grusr) + 1;
    }

    usedbuf = len;

    /*  substitute login names (if any) for mapped users */
    new_grmem = fixup_gr_mem(nm, (const char **)entry->gr_mem,
                             buf, &usedbuf, errp);
    buf += usedbuf;
    len -= usedbuf;
    if (errp) {
        if (*errp == ERANGE)
            ret = NSS_STATUS_TRYAGAIN;
        else if (*errp == ENOENT)
            ret = NSS_STATUS_UNAVAIL;

    } else if (len < 0) {
        *errp = ERANGE;
        ret = NSS_STATUS_TRYAGAIN;
    }

    if (*errp)
        goto done;
    *result = *newg;
    if (new_grmem)
        result->gr_mem = new_grmem;
    else {
        char **sav, **entgr, *usrbuf;
        len -= (members + 1) * sizeof *new_grmem;
        len -= memlen;
        if (len < 0) {
            *errp = ERANGE;
            ret = NSS_STATUS_TRYAGAIN;
            goto done;
        }
        sav = result->gr_mem = (char **)buf;
        buf += (members + 1) * sizeof *new_grmem;
        usrbuf = buf;

        for (entgr = entry->gr_mem; entgr && *entgr; entgr++, sav++) {
            *sav = usrbuf;
            usrbuf += strlen(*entgr) + 1;
            strcpy(*sav, *entgr);
        }

        *sav = NULL;
    }
    ret = NSS_STATUS_SUCCESS;
 done:
    return ret;
}

/*
* No locking needed because our only global is the dirent * for
* the runuser directory, and our use of that should be thread safe
*/
__attribute__((visibility("default")))
enum nss_status _nss_tacplus_getgrent_r(struct group *gr_result,
                                        char *buffer, size_t buflen,
                                        int *errnop)
{
    enum nss_status status = NSS_STATUS_NOTFOUND;
    struct group *ent;
    int ret = 1;
    int localerr;

    if (!gr_result) {
        if (errnop)
            *errnop = EFAULT;
        return status;
    }

    ret = get_config(errnop, 1);
    if(ret)
        return errnop && *errnop == ENOENT ? NSS_STATUS_UNAVAIL : status;

    if (!grent) {
        status = _nss_tacplus_setgrent();
        if (status != NSS_STATUS_SUCCESS)
            return status;
    }

    ent = fgetgrent(grent);
    if (!ent) {
        int e = errno;
        if (ferror(grent)) {
            syslog(LOG_WARNING,
                   "%s: error reading group information: %m", nssname);
            errno = e;
        } else
            errno = 0;
        return status;
    }
    ret = fixup_grent(ent, gr_result, buffer, buflen, &localerr);
    if (errnop)
        *errnop = localerr;
    return ret;
}

__attribute__((visibility("default")))
enum nss_status _nss_tacplus_getgrnam_r(const char *name, struct group *gr,
                                        char *buffer, size_t buflen,
                                        int *errnop)
{
    enum nss_status status = NSS_STATUS_NOTFOUND;
    int ret;
    struct group *ent;
    int localerr;

    if (!gr) {
        if (errnop)
            *errnop = EFAULT;
        return status;
    }

    ret = get_config(errnop, 1);
    if(ret)
        return errnop && *errnop == ENOENT ? NSS_STATUS_UNAVAIL : status;

    if (_nss_tacplus_setgrent() != NSS_STATUS_SUCCESS)
        return status;

    for (ent = fgetgrent(grent); ent; ent = fgetgrent(grent)) {
        if (!strcmp(ent->gr_name, name)) {
            status = fixup_grent(ent, gr, buffer, buflen, &localerr);
            if (errnop)
                *errnop = localerr;
            break;
        }
    }

    return status;
}

__attribute__((visibility("default")))
enum nss_status _nss_tacplus_getgrgid_r(gid_t gid, struct group *gr,
                                        char *buffer, size_t buflen,
                                        int *errnop)
{
    int ret;
    enum nss_status status = NSS_STATUS_NOTFOUND;
    struct group *ent;
    int localerr;

    if (!gr) {
        if (errnop)
            *errnop = EFAULT;
        return status;
    }

    ret = get_config(errnop, 1);
    if(ret)
        return errnop && *errnop == ENOENT ? NSS_STATUS_UNAVAIL : status;

    if (_nss_tacplus_setgrent() != NSS_STATUS_SUCCESS)
        return status;

    for (ent = fgetgrent(grent); ent; ent = fgetgrent(grent)) {
        if (ent->gr_gid == gid) {
            status = fixup_grent(ent, gr, buffer, buflen, &localerr);
            if (errnop)
                *errnop = localerr;
            break;
        }
    }

    return status;
}
