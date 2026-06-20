---
name: internal-docs
description: Process a task or design document from the NeST_internal_docs repository into code. Trigger whenever the user points to a specific file in ~/code/NeST_internal_docs/tasks/ or ~/code/NeST_internal_docs/designs/, or says things like "let's work on this task", "implement this spec", "pick up this work order", or otherwise references a named .md file from those directories. Does not cover investigation documents (~/code/NeST_internal_docs/investigations/), which require separate user guidance.
---

# Internal Docs

Process a task or design document from the NeST_internal_docs repository into code.

## Phase 1: Preparation

Complete all the following steps fully before starting implementation:

* Read the document for instructions.
* Read the frontmatter of the document for meta-data such as connected tasks.
* Refer to `~/code/NeST_internal_docs/CLAUDE.md` for info on frontmatter, querying the documentation, and for an entry into source code documentation.
* Read `~/code/NeST_internal_docs/api/` for high-level overviews of relevant source files. The API docs are curated summaries — read them before diving into source files to avoid rabbit-holing; only open a source file if relevant questions remain after reading the API doc.
* Interview the user to clarify any ambiguity in the task. The goal is to avoid surprising the user with design decisions they'd have made differently. An interview is not strictly necessary if the task is well-contained and well-specified; use judgment. Interview when for example:
  * Decisions already in the document have wider-reaching consequences than the document lets on.
  * The document does not make a required nontrivial decision, leaving it to the implementer.
* Set up task tracking for the remaining steps.

## Phase 2: Implementation

Unless otherwise noted, implementing a task also means developing tests for it. The exception is tasks that do not add new functionality **and** are sufficiently exercised by existing tests. It is your call whether to go implementation-first or tests-first.

* Write any tests.
* Implement the task.
* Break work into steps as appropriate. Whenever a clean but nontrivial intermediate state exists — one with green tests and coherent behaviour — treat it as its own step and commit it.

## Phase 3: Wrap-up

* Verify all tests are green. Debug as needed. Do not simplify or "fix" tests to make them pass — tests express intent, and a failing test is a signal about the implementation, not the test. If you believe a test is genuinely wrong, raise it with the user and make your case.
* Once all tests are green and the feature works as intended, commit the changes with a simple, one-sentence commit message. If the task was broken into intermediate steps with green tests, add commits for those too.
* Update the task documentation. Refer to `~/code/NeST_internal_docs/CLAUDE.md` for guidance. Specifically:
  * Adjust the frontmatter to reflect the changed status of the task.
  * Record any major design decisions in the prose section.
  * If API changes affect files described in `~/code/NeST_internal_docs/api/`, update those docs accordingly.
  * Commit the documentation changes, referencing the source repository commit hash.
