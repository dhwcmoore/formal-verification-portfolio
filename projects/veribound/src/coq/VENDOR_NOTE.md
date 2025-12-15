## Vendor note

Your working tree includes `vendor/flocq/` and many compiled artefacts.
For GitHub, prefer one of these:

1) Use Flocq as an opam dependency (cleanest), OR
2) Add Flocq as a git submodule, OR
3) Vendor only the source `.v` files (no `.vo/.vos/.vok/.glob`), with licence preserved.

This export excludes `vendor/` by default to keep the repo light and readable.
