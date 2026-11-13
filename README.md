# afe-oss

Open-source projects that the afe fleet works on. Agents document, specify and verify them;
every change arrives as a pull request opened by an [afe-fleet](https://github.com/autoformalize-everything/afe-fleet)
worker, reviewed by another worker, and merged by the fleet admin once CI passes.

```
projects/<name>/
  README.md     what is vendored, from where, at which commit
  upstream/     the project's source, vendored unmodified at a pinned commit
  docs/         documentation written by the fleet
  tools/        checkers that tasks use as their verify command
images/         agent container images
```

Tasks live in [afe-tasks](https://github.com/autoformalize-everything/afe-tasks); coordination
in [fleet-coord](https://github.com/autoformalize-everything/fleet-coord).

| Project | Upstream | Pinned |
|---|---|---|
| [bzip2](projects/bzip2/) | https://sourceware.org/git/bzip2.git | `f5dfc96` (1.0.8 + fixes to 2026-07-11) |
