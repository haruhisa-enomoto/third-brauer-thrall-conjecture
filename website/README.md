# Mathematical website

The site presents Theorem A and its corollaries, the independent statement, a
proof guide, a library overview and the searchable Lean API.

Build and check locally from the repository root:

```sh
python3 scripts/build_website.py
python3 scripts/check_website.py
python3 -m http.server 8000 --directory _site --bind 127.0.0.1
```

Generate the API first through the separate [docbuild project](../docbuild/README.md).

## Publish

The public URL is <https://haruhisa-enomoto.github.io/third-brauer-thrall-conjecture/>.
Repository **Settings → Pages → Source** must be **GitHub Actions**. After
committing and pushing source changes to `main`, run

```sh
python3 scripts/publish_website.py
```

The publisher rebuilds and checks the site, requires an API generated from the
current Lean source, and pushes the output and the
[Pages workflow](../.github/workflows/pages.yml) to the `gh-pages` branch from a
temporary clone. That push starts the deployment. No Lean build is performed.
