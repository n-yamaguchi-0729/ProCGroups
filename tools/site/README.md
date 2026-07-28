# ProCGroups documentation publisher

This directory contains the reproducible publisher for the standalone
ProCGroups v2 documentation site.

Run from this directory:

```powershell
python generate.py
```

The publisher reads only `Lean4/ProCGroups.lean` and
`Lean4/ProCGroups/**/*.lean` from this ProCGroups project. It builds and
validates a complete temporary site before replacing the contents of the
sibling `n-yamaguchi-0729.github.io/ProCGroups_pages` directory.
It also regenerates the Pages repository's root `sitemap.xml` from the current
homepage files and generated ProCGroups HTML pages, so removed legacy URLs
cannot remain in the sitemap.

Release identity, source commit, repository URL, module count, and public URL
are pinned in `site_config.json`. Update that file deliberately for a future
release; do not edit generated HTML by hand.
