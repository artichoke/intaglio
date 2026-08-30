# Publishing

This crate is published to [crates.io] by the
[`publish.yaml`](../.github/workflows/publish.yaml) GitHub Actions workflow.
Publishing uses OpenID Connect (OIDC) trusted publishing. The repository does
not store a long-lived crates.io API token.

## Trust configuration

The crates.io trusted publisher must match this tuple exactly:

| Setting           | Value               |
| ----------------- | ------------------- |
| Crate             | `intaglio`          |
| GitHub owner      | `artichoke`         |
| GitHub repository | `intaglio`          |
| Workflow          | `publish.yaml`      |
| Environment       | `crates-io-publish` |

The GitHub `crates-io-publish` environment accepts deployments only from tags
matching `v*.*.*`. Repository rulesets make tags immutable after creation.

The trusted publisher and GitHub environment are external configuration. Audit
them against this document when changing release automation.

## Prepare a release

1. Open a release pull request that updates the version in `Cargo.toml` and
   every repository-owned copy of that version, including `html_root_url`,
   examples, and lockfiles when present.
2. Run the repository's formatting, linting, and test commands.
3. Run `cargo publish --dry-run` and inspect the packaged file list.
4. Merge the release pull request only after its required checks pass.
5. Wait for CI on the merged `trunk` commit to complete successfully.

## Publish

Create the release tag from the merged `trunk` commit. Tags use the exact
`vX.Y.Z` form required by the workflow.

```sh
git switch trunk
git pull --ff-only
git tag -s "vX.Y.Z" -m "vX.Y.Z"
git push origin "vX.Y.Z"
```

The publish workflow verifies that the tag has exact semantic-version syntax,
that the tag version matches `Cargo.toml`, and that CI succeeded for the tagged
commit. It then exchanges its GitHub OIDC identity for a short-lived crates.io
credential and runs `cargo publish`.

Monitor the Publish workflow through completion, then verify the new version on
crates.io and docs.rs.

## Failed releases

Do not move or delete a release tag. Tag immutability is an intentional release
integrity control.

If publishing fails before crates.io accepts the version, fix the failure on
`trunk` and prepare a new patch release. Before retrying a transient failed
workflow, confirm that crates.io does not already contain the version and that
the tag still points to the intended, green commit.

[crates.io]: https://crates.io/crates/intaglio
