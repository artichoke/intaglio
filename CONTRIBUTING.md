# Contributing to Artichoke – Intaglio

👋 Hi and welcome to [Artichoke]. Thanks for taking the time to contribute!
💪💎🙌

Artichoke aspires to be a [recent MRI Ruby][mri-target]-compatible
implementation of the Ruby programming language. [There is lots to do].

[mri-target]:
  https://github.com/artichoke/artichoke/blob/trunk/RUBYSPEC.md#mri-target

Intaglio is used to implement storage for the [`Symbol` class][ruby-symbol] and
the constant name table in Artichoke interpreter state.

If Artichoke does not run Ruby source code in the same way that MRI does, it is
a bug and we would appreciate if you [filed an issue so we can fix it]. [File
bugs specific to Intaglio in this repository].

If you would like to contribute code to Intaglio 👩‍💻👨‍💻, find an issue that looks
interesting and leave a comment that you're beginning to investigate. If there
is no issue, please file one before beginning to work on a PR. [Good first
issues are labeled `E-easy`].

## Discussion

If you'd like to engage in a discussion outside of GitHub, you can [join
Artichoke's public Discord server].

## Setup

Intaglio includes Rust and Text sources. Developing on Intaglio requires
configuring several dependencies.

### Rust Toolchain

Intalgio depends on Rust and several compiler plugins for linting and
formatting. Intaglio is guaranteed to build on the latest stable release of the
Rust compiler.

#### Installation

The recommended way to install the Rust toolchain is with [rustup]. On macOS,
you can install rustup with [Homebrew]:

```sh
brew install rustup-init
rustup-init
```

Once you have rustup, you can install the Rust toolchain needed to compile
Intaglio:

```sh
rustup toolchain install stable
rustup component add rustfmt
rustup component add clippy
```

To update your stable Rust compiler to the latest version, run:

```sh
rustup update stable
```

### Rust Crates

Intaglio depends on several Rust libraries, or crates. Once you have the Rust
toolchain installed, you can install the crates specified in
[`Cargo.toml`](Cargo.toml) by running:

```sh
cargo build
```

### Ruby

Intaglio requires a recent Ruby and [bundler] for development tasks. The
[`.ruby-version`](.ruby-version) file in this repository specifies the preferred
Ruby toolchain.

If you use [RVM], you can install Ruby dependencies by running:

```sh
rvm install "$(cat .ruby-version)"
gem install bundler
```

If you use [rbenv] and [ruby-build], you can install Ruby dependencies by
running:

```sh
rbenv install "$(cat .ruby-version)"
gem install bundler
rbenv rehash
```

The [`Gemfile`](Gemfile) in this repository specifies several dev dependencies.
You can install these dependencies by running:

```sh
bundle install
```

[rvm]: https://rvm.io/
[rbenv]: https://github.com/rbenv/rbenv
[ruby-build]: https://github.com/rbenv/ruby-build

Intaglio uses [`rake`](Rakefile) as a task runner. You can see the available
tasks by running:

```sh
bundle exec rake --tasks
```

To lint Ruby sources, Intaglio uses [RuboCop]. RuboCop runs as part of the
`lint` task. To run RuboCop by itself, invoke the `lint:rubocop` task.

```sh
bundle exec rake lint
bundle exec rake lint:rubocop
```

### Node.js

Node.js is an optional dependency that is used for formatting text sources with
[prettier].

Node.js is only required for formatting if modifying the following filetypes:

- `md`
- `yaml`
- `yml`

You will need to install [Node.js]. The [`.ruby-version`](.ruby-version) file in
this repository specifies the preferred Node.js toolchain.

On macOS, you can install Node.js with [Homebrew]:

```sh
brew install node
```

## Linting

To lint and format Rust sources run:

```sh
bundle exec rake lint:clippy
bundle exec rake fmt:rust
```

To lint and format text sources run:

```sh
bundle exec rake fmt:text
```

## Testing

A PR must have new or existing tests for it to be merged. The [Rust book chapter
on testing] is a good place to start.

To run tests:

```sh
cargo test
```

`cargo test` accepts a filter argument that will limit test execution to tests
that substring match. For example, to run all of the tests for drop behavior:

```sh
cargo test drop
```

Tests are run for every PR. All builds must pass before merging a PR.

## Updating Dependencies

### Rust Crates

Version specifiers in `Cargo.toml` are NPM caret-style by default. A version
specifier of `4.1.2` means `4.1.2 <= version < 5.0.0`.

To see what crates are outdated, you can use [cargo-outdated].

If you need to pull in an updated version of a crate for a bugfix or a new
feature, update the version number in `Cargo.toml`. See
[artichoke/artichoke#548] for an example.

Regular dependency bumps are handled by [@dependabot].

[artichoke]: https://github.com/artichoke
[there is lots to do]: https://github.com/artichoke/artichoke/issues
[ruby-symbol]: https://ruby-doc.org/core-3.1.2/Symbol.html
[filed an issue so we can fix it]:
  https://github.com/artichoke/artichoke/issues/new
[file bugs specific to intaglio in this repository]:
  https://github.com/artichoke/intaglio/issues/new
[good first issues are labeled `e-easy`]:
  https://github.com/artichoke/intaglio/labels/E-easy
[join artichoke's public discord server]: https://discord.gg/QCe2tp2
[rustup]: https://rustup.rs/
[homebrew]: https://docs.brew.sh/Installation
[bundler]: https://bundler.io/
[rubocop]: https://github.com/rubocop-hq/rubocop
[prettier]: https://prettier.io/
[node.js]: https://nodejs.org/en/download/package-manager/
[rust book chapter on testing]:
  https://doc.rust-lang.org/book/ch11-00-testing.html
[cargo-outdated]: https://github.com/kbknapp/cargo-outdated
[artichoke/artichoke#548]: https://github.com/artichoke/artichoke/pull/548
[@dependabot]: https://dependabot.com/
