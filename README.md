# EquivcheckEr

- Uses property based testing to check the equivalence of code refactored by Wrangler
- Compares folders or commits of the same codebase with the original and refactored code (git)

## Disclaimer

Randomized testing in itself can never be sufficient for eliminating the possibility of bugs.
EquivcheckEr will never report false positives, but its entirely possible for it to omit true positives,
so it cannot replace engineering discipline.
As Dijkstra once said:
> "Testing shows the presence, not the absence of bugs"

## Dependencies

- Erlang/OTP 26 or later
- [Wrangler](https://refactoringtools.github.io/docs/wrangler/)
- [PropEr](https://proper-testing.github.io/)
- Jsone
- Git: The git cli client has to be installed
- Dialyzer, Typer (usually packaged together with Erlang)

## Installing

Just grab the latest [release](https://github.com/harp-project/EquivcheckEr/releases/latest) and put it somewhere on your `$PATH` (e.g.: `~/.local/bin`).
You also have to add execute permissions. (`chmod +x equivchecker`)

## Usage

To run the check, you can specify which folders or commits you want to compare like this

`$ equivchecker <original_source> <refactored_source>`

`$ equivchecker -c <original_commit> <refactored_commit>`

The `-c (or --commit)` flag tells equivchecker to use commits instead of folders.

You can also specify a single commit or folder, in which case the content of the current directory will be compared to it:

`$ equivchecker <original_folder>`

`$ equivchecker -c <original_commit>`

You can even omit both arguments:

`$ equivchecker`

In this case, the current directory will be compared to the currently checked out commit (HEAD).

### JSON

It's possible to get the output formatted as JSON:

`$ equivchecker --json`

### Statistics

Statistical information about the tests can be generated with `-s` or `--statistics`:

`$ equivchecker --statistics`

## Acknowledgments

We would like to thank the [Erlang Ecosystem Foundation](https://erlef.org/) for generously funding the development of this project.
Their support has been invaluable and has allowed us to bring this project to life.
