# Persistent todo CLI

[`examples/todo-cli`](../examples/todo-cli) is a project-shaped Kush application
with plain-file storage. It is separate from the session-only terminal board in
[todo.md](todo.md).

```text
examples/todo-cli/
  Kush.toml
  src/main.kush
  src/cli.kush
  src/store.kush
  tests/main.kush
```

`Kush.toml` names the package `todo_cli` and points at `src/main.kush`. Module
headers are `todo_cli`, `todo_cli.cli`, `todo_cli.store`, and
`todo_cli.tests.main`, which is the layout expected by the project module
index. The source tree is checked by the same compiler as a single file; the
integration test supplies an equivalent module index while this checkout does
not yet contain the project loader.

## Usage

```sh
kush run --file examples/todo-cli/src/main.kush -- list
kush run --file examples/todo-cli/src/main.kush -- add Buy milk
kush run --file examples/todo-cli/src/main.kush -- list
kush run --file examples/todo-cli/src/main.kush -- done 1
kush run --file examples/todo-cli/src/main.kush -- remove 1
```

Inside a project checkout built with the project workflow, the same arguments
are forwarded unchanged after `--` by `ProgramInvocation`; the native program
reads them through the host `ENV` builtins. The file defaults to `todo.txt` in
the current directory, or to `KUSH_TODO_FILE` when that environment variable is
set. `--file PATH` before the command overrides both.

```text
todo [--file PATH] <command> [args]

  add <title...>   add a task
  list             list tasks
  done <id>        mark a task complete (1-based line)
  remove <id>      remove a task
  --help
```

Titles are joined from the remaining arguments with single spaces. They may
contain arbitrary non-NUL bytes except `|`, CR, and LF so one task stays on one
line. IDs are 1-based line numbers and can change after a removal.

## Storage and failure behavior

Each task is one line:

```text
0|Buy milk
1|Ship code
```

`0` is open and `1` is done. The whole file is validated before any rewrite.
A missing file lists as empty. A malformed file, unknown command, missing title,
missing argument, or out-of-range id exits with status 2 and leaves the file
unchanged. Host I/O failures print the errno and exit with status 1. Reads are
bounded to 64 KiB; a larger file reports `EFBIG` and is not rewritten.

Writes go to `<path>.tmp` and are installed with `FS.rename`, so a successful
command replaces the file atomically on the target Linux filesystem. A failed
write or rename removes the temporary file, prints the host error, and exits
with status 1. The program never writes outside the chosen path.

This is a single-user local CLI, not a database: there is no locking, crash
journal, durability `fsync`, concurrent writer protocol, or Windows rename
compatibility. It is an application example for the checked host APIs and the
project-shaped source layout, not a claim that those broader facilities exist.

## Tests

The Rust integration test
[`crates/kush/tests/todo_app.rs`](../crates/kush/tests/todo_app.rs) builds the
app through the reference evaluator and the native backend, then compares
output, exit status, persisted contents, reloads, invalid files, `--file`, and
`KUSH_TODO_FILE` in isolated temporary directories. The project-shaped
`tests/main.kush` exercises the store validator and rewrite helpers under the
project test workflow.
