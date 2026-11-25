# HarborMaster in TLA+

Formal models of the rollback-detection protocol from

> Shubham Mishra, Alexander Thomas, Nurzhan Abdrassilov, Kaiyuan Chen, Natacha Crooks, John Kubiatowicz.
> **HarborMaster: Rollback Detection for Trusted Distributed Computing.** PVLDB 19(9): 2126–2139, 2026.

The protocol is specified in pure TLA+ and checked exhaustively with the TLC model checker. The model is built in stages: each stage is a separate spec that extends the previous one, so every stage stays a self-contained, checked result.

---

## TL;DR

| Stage | Spec | What it adds | Result |
|---|---|---|---|
| 1 | `RDCommit.tla` | Logging and RD-Commit on f+1 votes (§4.2) | ✅ Holds (227 states) |
| 1b | `RDCommitFaults.tla` | + message loss, crashes, restarts | ✅ Holds (3,081,312 states) |
| 2a | `Rollback.tla` | + storage-server rollback attacks and detection (§3.3, §4.3) | ❌ **Silent loss under the paper's crash assumption.** ✅ Holds under a stronger one. |

**Main finding.** With at most *f* storage servers down *at any given time* (§3.1), TLC finds a 10-step trace in which the f+1 servers that voted for a committed entry crash **one after another**, each having its disk rolled back. Every restart wipes TEE memory, so the entry ends up on no disk, provable by no running server, and undetected. The guarantee holds if at most *f* servers **ever** lose their memory. The auditor and reconfiguration, which are not modeled yet, may close this gap.

---

## Background

HarborMaster protects applications running in Trusted Execution Environments (TEEs). A TEE protects **memory** but not **disk**, so a malicious cloud provider can replace a node's persistent state with a stale copy: a **rollback attack**.

HarborMaster's defense:

1. Before every read or write to persistent state, a **worker** creates a hash-chained log entry and sends it to **N = 2f + 1 storage servers**.
2. Each server stores the entry only if it directly extends its chain, then replies with a **vote**.
3. After **f + 1 votes**, the entry is **RD-Committed** (Rollback-Detectable Committed), and only then is the operation performed.
4. Each server remembers its latest entry in **TEE memory**. If its disk is missing an entry that memory says exists, it reports a rollback.
5. An **auditor** replays the logs to detect rollbacks of worker state through causality violations (§4.4, not modeled yet).

The paper's key distinction (§3.4):

- **Retrievable**: an entry's contents can still be read from some server.
- **Provable**: some non-crashed server can still prove the entry existed.

**Definition 1.** An entry is RD-Committed when it and all entries before it are provable. The goal is that a committed entry can never disappear **without a trace**.

---

## Repository layout

```
harbormaster-tla/
├── harbormaster/
│   ├── RDCommit.tla         Stage 1:  logging + RD-Commit
│   ├── RDCommit.cfg
│   ├── RDCommitFaults.tla   Stage 1b: + message loss, crashes, restarts
│   ├── RDCommitFaults.cfg
│   ├── Rollback.tla         Stage 2a: + storage rollback attacks and detection
│   ├── Rollback.cfg
│   └── NOTES.md             Working notes and modeling decisions
├── learning/
│   └── wire/
│       ├── WireTransfer.tla Warm-up: the learntla.com bank-transfer race in pure TLA+
│       └── WireTransfer.cfg
