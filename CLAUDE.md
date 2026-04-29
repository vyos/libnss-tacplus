# CLAUDE.md

## Project purpose

NSS plugin (`libnss_tacplus.so`) that resolves `getpwnam` lookups for TACACS+-authenticated users that have no local `/etc/passwd` entry. Maps remote TACACS+ users onto the local `tacacs0..15` stub accounts and pulls home/uid/gid via `libtacplus-map`. Used together with `libpam-tacplus` for full TACACS+ login flow on VyOS.

## Tech stack

- C, GNU autotools (`configure.ac`, `Makefile.am`, `aclocal.m4`).
- Debian packaging in `debian/` (debhelper >= 9, autotools-dev, `libtac-dev`, `libtacplus-map-dev`, `libaudit-dev`, `libpam-tacplus-dev`).
- License: GPL-2.0 (per `COPYING`).

## Build / test / run

```sh
./auto.sh                 # autoreconf (generates ./configure)
./configure
make
sudo make install         # installs libnss_tacplus.so + tacplus_nss.conf
dpkg-buildpackage -us -uc # debian package build
```

No in-tree test suite — exercised end-to-end on a VyOS image via `pam_tacplus` login.

## Repository layout

- `nss_tacplus.c`, `nss_tacplus.h` — NSS module entry points.
- `tacplus_nss.conf`, `tacplus_nss.conf.5` — config file + man page.
- `debian/` — Debian packaging.

## Cross-repo context

Pre-dep of the `vyos-1x` runtime auth stack. Built via `VyOS-Networks/vyos-build-packages` and shipped in the ISO from `vyos/vyos-build`. Calls into `libtacplus-map` (mapping helper) and the `libtac` library produced by `libpam-tacplus`. Companion repos: `libpam-tacplus`, `libtacplus-map`, `libnss-mapuser`, `libpam-radius-auth`.

## Conventions

- Default branch `master` (forked from `daveolson53/libnss-tacplus`).
- Commit / PR title format: `component: T12345: description` (Phorge task ID at https://vyos.dev) — enforced if PR-message workflow is added later. No workflow files currently in `.github/workflows/`.
- Treat as upstream-vendored: keep diffs against fork minimal; new functionality belongs in `libtacplus-map` or `libpam-tacplus`.

## Mirror relationship

Mirror twin: `VyOS-Networks/libnss-tacplus`. Canonical side is here. The mirror pipeline (`vyos/.github/.github/workflows/pr-mirror-repo-sync.yml`) is **not** wired up for this repo today (no workflows in `.github/workflows/`).

## Notes for future contributors

- README is upstream's `libnss_tacplus v1.0.1` text (June 2016) — do not assume it documents VyOS-specific patches.
- Outbound webhook to `hooks.zapier.com` is configured at the repo level (audit baseline 2026-04-18).
- LTS-only changes go to `sagitta`/`circinus`/`equuleus` branches if/when created; today only `master` exists.
