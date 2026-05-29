# Automation Conventions

Automations should keep machine-authored output distinguishable from human
feedback so follow-up runs can learn from the right signals.

Automation-authored pull request comments must start with the stable prefix
`Codex automation note:`. Treat comments with that prefix as automation state,
not human feedback for automation learning loops.

Document each scheduled automation in this directory and keep the actual
automation prompt slim. The prompt should identify the role and tell the
automation to read and follow its documentation in this repository.

Current automations:

- [GitHub Actions Runner Images](./github-actions-runner-images.md)
