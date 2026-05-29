# GitHub Actions Runner Images Automation

The GitHub Actions runner images automation is a scheduled repository
maintenance role for keeping workflow runner labels aligned with GitHub-hosted
runner image support status. It should catch upcoming image migrations,
deprecations, brownouts, and retirements early enough that this repository's CI
keeps exercising maintained Linux, Windows, and macOS targets.

The automation must read `docs/automations/README.md` and this document before
running. Human feedback on any output it produces, including inbox follow-ups,
pull request comments, review decisions, failed validation, or missed runner
image changes, should be reviewed and used to update this document before
repeating the same class of issue. Automation-authored pull request comments
must start with the stable prefix `Codex automation note:`. Treat comments with
that prefix as automation state, not human feedback for this learning loop.

## Schedule

Run once per week against this repository. GitHub runner image changes are
announced with lead time, so a weekly cadence is enough.

## Scope

Review GitHub Actions workflow files under `.github/workflows/`, with emphasis
on `runs-on` labels and runner-image-sensitive assumptions.

This repository is a portable Rust string interner crate. The most important
coverage is:

- current generally available Ubuntu, Windows, and macOS images;
- explicit OS labels where stable, explainable coverage matters;
- 64-bit Linux, Windows, and macOS build coverage;
- 32-bit Linux and Windows build coverage;
- MSRV, Miri, leak sanitizer, coverage, publish, repository label, lint, and
  formatting jobs that should avoid surprise OS changes unless the workflow
  intentionally tracks `*-latest`.

Do not update pinned GitHub Actions versions in this automation. Dependabot owns
GitHub Actions dependency updates.

## Sources

Use authoritative current sources. Do not rely on memory for runner image state.
At minimum, inspect:

- the `actions/runner-images` README for currently available image labels;
- open issues in `actions/runner-images` with the `Announcement` label;
- GitHub-hosted runner documentation when label semantics or hardware
  availability are unclear;
- this repository's recent CI runs if a label appears questionable.

When a source is date-sensitive, include concrete dates in the inbox summary and
pull request description.

## Decision Rules

Prefer explicit OS labels over `*-latest` for jobs where stable, explainable
coverage matters. `*-latest` is acceptable only when the job is intentionally
exercising GitHub's moving default.

For cross-platform build coverage, keep the matrix on maintained GA images for
Ubuntu, Windows, and macOS. When a new OS image becomes GA, add it before the
previous default migrates. When an older image enters deprecation, remove it
before brownouts begin unless there is a documented compatibility reason to keep
it.

For MSRV, Miri, leak sanitizer, coverage, publish, repository label, lint,
formatting, and documentation jobs, prefer explicit maintained labels unless the
workflow intentionally follows a moving default.

## Changes

If runner image state indicates no repository change is needed, do not create a
branch, commit, push, or pull request. Open an inbox item with the checked
labels, source links, and next relevant dates.

If changes are needed, edit the relevant workflow files and keep the diff scoped
to runner image maintenance. Then create one commit and one pull request.

If workflow matrix labels change, check whether required status-check contexts
in GitHub branch rulesets also need to change. The `gh ruleset` command can list
and view rulesets, but ruleset updates currently go through `gh api`:

```sh
gh ruleset list --repo artichoke/intaglio
gh api repos/artichoke/intaglio/rulesets/<ruleset-id> \
  --jq '.rules[] | select(.type == "required_status_checks").parameters.required_status_checks[].context'
```

When the required-check list needs updating, fetch the full ruleset, build an
update payload from its editable fields, update the `required_status_checks`
contexts, and put the ruleset back:

```sh
gh api repos/artichoke/intaglio/rulesets/<ruleset-id> > /tmp/intaglio-ruleset.json
jq '{name, target, enforcement, conditions, bypass_actors, rules}' \
  /tmp/intaglio-ruleset.json > /tmp/intaglio-ruleset.update.json
# Edit /tmp/intaglio-ruleset.update.json so required check contexts match the
# workflow job names produced by the new matrix.
gh api -X PUT repos/artichoke/intaglio/rulesets/<ruleset-id> \
  --input /tmp/intaglio-ruleset.update.json
```

Ruleset edits are repository configuration changes, not git changes. Mention any
ruleset contexts inspected or updated in the pull request and inbox summary. If
the automation cannot update the ruleset because of permissions, open the pull
request anyway and lead the inbox item with the exact required-check contexts
that need manual ruleset changes.

Pull requests from this automation must include the `A-build` and `C-automation`
labels, plus the `codex` label. Include source links for runner image
announcements and explain any upcoming deprecation, brownout, or latest label
migration dates.

Do not enable auto-merge if:

- a runner label is in beta or preview;
- a change drops an OS family without replacement;
- a recent CI run failed for reasons that could be related to the runner image;
- the source announcements are ambiguous or internally inconsistent.

For low-risk mechanical label updates with passing validation, enabling
auto-merge is acceptable.

## Validation and Summary

For workflow-only edits, run:

```sh
git diff --check
pnpm exec prettier --check '**/*'
```

If `actionlint` is available, run it against the changed workflows. If it is not
available, say so in the inbox summary and pull request.

If Rust code or manifests are touched, also run the relevant Rust checks for the
touched files. Runner image maintenance should not normally require Rust source
changes.

Open an inbox item after every run summarizing:

- runner labels reviewed;
- current GitHub support state for those labels;
- source links used;
- upcoming migration, deprecation, brownout, or retirement dates;
- changes made or why no change was needed;
- branch ruleset required-check contexts inspected or updated;
- validation run and any skipped checks;
- pull request and auto-merge status, if a pull request was opened.
