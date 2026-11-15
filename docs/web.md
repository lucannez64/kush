# A web framework written in Kush

Status: design approved by the user 2026-11-14 (WEB-DESIGN); the decisions
are at the end. Nothing else is implemented. Plan nodes are named in brackets; dependencies
are in `plan/plan.json` (prefix `WEB-`).

Goal: an HTTP server framework written in Kush, in the family of Axum and
Phoenix, where the language checks what other frameworks leave to
convention: every request gets exactly one response, a handler can only
reach the services its effect row names, and user input cannot reach HTML
unescaped. Running Kush in the browser (WebAssembly) is a separate project
and is not planned here.

## What exists

- `std.json` (parser and serializer, written in Kush), `std.text`,
  `std.bytemap`, `std.collections`.
- `std.sys`: one C stub per system call, the safe wrapper in Kush, reference
  evaluator shims (STD-SYS-FOREIGN, EVAL-FOREIGN-SHIMS). New socket calls
  follow the same pattern.
- Linear resources (`std.file`, `media` windows): the checker rejects a
  handle that is leaked, closed twice or used after close.
- OS threads with atomics and bounded channels (`Thread.scope`), and
  cooperative tasks (`Task.scope`, the `suspend` effect).
- Effect handlers: deep, one-shot by default, declared operations visible to
  called functions, abortive handlers.
- `std.http`: a one-shot HTTP/1.1 *client* over `NET.tcp_exchange`.
- kush-kv, a crash-safe key-value store, for the first demo's storage.

## What is missing

1. **Server sockets** (done, WEB-NET). `std.net` has a linear `Listener`
   (`listen`, `local_port`, `accept`, `close_listener`) and a linear `Conn`
   (`connect`, `read`, `write`, `shutdown`, `set_nodelay`, `close`), so a
   socket that is leaked, closed twice or used after close is a compile
   error. They still block the thread, with timeouts; WEB-REACTOR makes them
   suspend a task. See [std-sys.md](std-sys.md).
2. **Nonblocking I/O.** [async.md](async.md) says it plainly: blocking I/O
   stalls the task scheduler, and tasks run on one OS thread. A server that
   holds thousands of connections needs a reactor that suspends a task on a
   read that would block.
3. **Task limits** (done, TASK-ID-REUSE). The native runtime allowed 255
   spawned tasks per run and 64 children per scope; it now reuses joined
   task slots, so the bound is live tasks.
4. **An HTTP server parser** with limits, chunked bodies and keep-alive.
5. **Automatic codecs** (below).
6. **TLS, cookies, crypto, a database driver, WebSockets.**

## Automatic codecs: the biggest language gap

Today every JSON encoder and decoder for a record would be written by hand.
A framework needs automatic codecs, which means either a derive mechanism or
the planned staging plus write-once formats (FORMATS-ROUNDTRIP). This is the
biggest gap in the language itself.

Two routes were considered:

- **Derive.** A compiler-provided `#[derive(Json)]` on records and enums
  that generates an `impl` of an encode/decode trait. Small to build,
  limited to the formats the compiler knows.
- **Staging.** Codecs as ordinary Kush library code that inspects a type's
  description and generates the parser and serializer through `Code<T>`
  (STAGING), with `parse(serialize(x)) == x` proved (FORMATS-ROUNDTRIP).
  More work, but any library can add a format, and the round trip is a
  theorem.

Decision: **staging**. There is no derive mechanism; WEB-CODECS waits for
STAGING and FORMATS-ROUNDTRIP and builds JSON codecs on the same format
descriptions. Until then, `std.json` gets typed field accessors
[WEB-JSON-FIELDS] so hand-written decoders stay short and report which field
was wrong.

## The framework

Illustrative syntax; the details belong to the implementation nodes.

```kush
effect Db: Query -> Rows;                 // a declared operation

fn list_todos(req: &Request, res: Responder) -> Unit ! {Db, io, alloc, panic} {
    let rows = perform Db(Query.all_todos());
    res.json(200, &todos_to_json(&rows))  // consumes the linear Responder
}

fn health(req: &Request, res: Responder) -> Unit ! {io, alloc} {
    res.text(200, &Bytes.from("ok"))     // no Db in the row: cannot query
}

fn main() -> Unit ! {io, alloc, panic, suspend} {
    let app = Router.new()
        .get("/todos", list_todos)
        .get("/health", health);
    with_kv_db("todos.kv", fn() { serve(&app, 8080) })  // a task per connection
}
```

### Every request is answered once [WEB-CORE]

`Responder` is `#[linear]`. A handler receives it by value and must consume
it on every path, with exactly one of `res.text`, `res.json`, `res.html`,
`res.status` or `res.stream`. Forgetting to answer on an error branch, or
answering twice, is a compile error. A handler that panics is answered with a
500 by the server loop, which owns the connection.

### Effect rows as permissions [WEB-EFFECTS]

Services are declared operations: `Db`, `CurrentUser`, `Log`, `Clock`. A
handler's row lists the ones it uses, and the checker rejects a `perform` the
row does not name. The router stores handlers at the application's row;
arrow subtyping accepts a handler with a smaller row, so `health` above is
checked against `{io, alloc}` when it is written and still fits the table.

Middleware is a handler around the request:

- authentication handles `CurrentUser` from the session cookie;
- a transaction handles `Db`, commits after `resume` returns and rolls back
  when the body aborts (abortive handlers exist);
- logging and timing wrap the request.

Tests install their own handlers: an in-memory `Db`, a fixed `Clock`, a
chosen `CurrentUser`. No mocking library, and the test runs in the reference
evaluator without a socket [WEB-TEST-CLIENT].

### Untrusted input and HTML [WEB-HTML]

Request text (path, query, headers, body) arrives as `Untrusted`. The `Html`
type has no public constructor from text: only `html.escape(&Untrusted)`,
`html.literal` (source literals) and the builder functions make one, so
`res.html` cannot receive unescaped input. A deliberate `html.trust(..)`
exists and is greppable.

### Routes [WEB-ROUTER]

Method plus path pattern (`/todos/{id}`), path parameters decoded and
range-checked before the handler runs (a malformed `id` is a 400, not a
handler branch), 404 and 405 with an `Allow` header. Typed request bodies
(`Json<NewTodo>`) come with codecs [WEB-EXTRACT].

## Server architecture

There is no blocking thread-pool server: the first server runs on the
reactor.

### An epoll reactor in the task scheduler [WEB-REACTOR]

Sockets are nonblocking. A read or write that returns `EAGAIN` registers the
descriptor with epoll and suspends the task (`suspend` effect); when no task
is runnable the scheduler sleeps in `epoll_wait` until a descriptor is ready
or the nearest timer expires. Timers (`Time.sleep` in a task, request
deadlines) go through the same wait. The reference evaluator keeps a
deterministic model: it polls ready descriptors in a fixed order, so tests
stay reproducible. This needs unlimited tasks over a program's life
[TASK-ID-REUSE].

The server runs one task per connection [WEB-SERVER]: accept, parse,
route, answer, keep-alive with an idle deadline, a handler panic answered as
500, graceful stop. Idle connections cost a suspended task, not a thread.

### One reactor per thread [WEB-MULTICORE]

Thread bodies may capture moved values and borrowed slice views only, and
tasks cannot cross threads, so instead of work stealing every thread runs
its own scheduler and reactor (THREAD-TASKS) with its own `SO_REUSEPORT`
listener. A connection lives and dies on one thread.

## HTTP/1.1 [WEB-HTTP-PARSE]

A parser over a borrowed byte view, with no I/O: request line, headers,
`Content-Length`, chunked transfer coding, `Connection` and keep-alive,
`Expect: 100-continue` refused for now. Hard limits on request-line length,
header count, header bytes and body size, each a 4xx, never a panic.
Duplicate or conflicting `Content-Length` and `Transfer-Encoding` headers
are rejected (request smuggling). The response writer emits the status line,
headers and body or chunks. Its bounds checks are meant to be proved; the
ones the prover leaves go to `kush fuzz` (PROOF-FUZZ). URL and query
decoding is separate [WEB-URL].

## Security and ecosystem

- **Crypto** [WEB-CRYPTO, done: [std-crypto.md](std-crypto.md)]: SHA-1
  (WebSocket handshake only), SHA-256, HMAC-SHA256, constant-time
  comparison, base64 and base64url, and a `getrandom` stub, in Kush with
  known-answer tests.
- **Cookies and sessions** [WEB-SESSIONS]: cookie parsing and
  `Set-Cookie`, signed session cookies, `CurrentUser` handled from them.
- **TLS** [WEB-TLS]: not written in Kush. Run a reverse proxy (Caddy,
  nginx) first. Later wrap rustls through `kush bindgen`: rustls has a
  sans-I/O API (bytes in, bytes out), so bridge ABI v1 is enough and no
  foreign callbacks are needed.
- **Database** [WEB-DB]: kush-kv for the demo; SQLite through a bindgen
  adapter as the first SQL store, handling `Db`.
- **WebSockets** [WEB-WEBSOCKET]: upgrade handshake, framing, ping/pong
  and close, as long-lived tasks on the reactor. Session-typed
  WebSocket protocols come after SESSION-NET [WEB-WS-SESSION].

## First demo [WEB-TODO-DEMO]

`examples/todo-web`: the todo list as a JSON API on kush-kv, served by the
reactor server, with hand-written codecs over `WEB-JSON-FIELDS`, the linear
`Responder`, a `Db` effect, middleware for logging, in-process tests, and a
`curl` script. It does not wait for staging, so it is the first thing a
stranger can run.

## Order

```
WEB-DESIGN (done)
├─ WEB-NET (done) ───────────────────────┐
│                     TASK-ID-REUSE ─────┴─ WEB-REACTOR ─┐
├─ WEB-HTTP-PARSE ── WEB-CORE ───────────────────────────┴─ WEB-SERVER ─┬─ WEB-MULTICORE (after THREAD-TASKS)
├─ WEB-URL ─────────────┴─ WEB-ROUTER ─ WEB-EFFECTS ─ WEB-TEST-CLIENT  ├─ WEB-TLS
├─ WEB-JSON-FIELDS                                                       ├─ WEB-WEBSOCKET (after WEB-CRYPTO)
│                                                                        │    └─ WEB-WS-SESSION (after SESSION-NET)
│      WEB-SERVER + WEB-TEST-CLIENT + WEB-JSON-FIELDS ─ WEB-TODO-DEMO
├─ WEB-HTML (after WEB-CORE)
├─ WEB-CRYPTO ─ WEB-SESSIONS (after WEB-EFFECTS)
└─ STAGING + FORMATS-ROUNDTRIP ─ WEB-CODECS ─ WEB-EXTRACT (after WEB-ROUTER)
WEB-EFFECTS ─ WEB-DB
```

`WEB-REVIEW` is an independent review once the demo, typed extractors,
sessions and HTML are in; `WEB` closes the track.

## Decisions (2026-11-14)

1. **Codecs: staging.** No derive mechanism; WEB-CODECS depends on STAGING
   and FORMATS-ROUNDTRIP.
2. **`Untrusted` is a distinct type**, not a grade on `Bytes`. A type works
   with today's checker and makes every conversion visible
   (`html.escape`, `Untrusted.validate`, `Untrusted.trust`); a grade would
   have to flow through every text function and through grade inference
   before it protected anything. A grade can be layered on later if text
   functions grow grade-polymorphic signatures.
3. **Handlers take a linear `Responder`:** `fn(&Request, Responder) -> Unit`.
   It is the only shape that streams, and "answered exactly once" is checked
   for streamed responses too. `fn(&Request) -> Response` can be offered as
   a helper that wraps it.
4. **No blocking v1 server.** The first server runs on the epoll reactor;
   WEB-NET, WEB-REACTOR and TASK-ID-REUSE are on the path to the demo.
