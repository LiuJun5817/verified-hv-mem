# verified-hv-mem
A modular, architecture-independent memory management library for Rust hypervisors, designed for reuse and formal verification with Verus.

## Code Submission with `git cz` (replace `git commit`)

see [commitizen.md](commitizen.md)

### Configuration

This project is already configured for Commitizen in `package.json`:

```json
"scripts": {
  "cz": "git-cz"
},
"devDependencies": {
  "commitizen": "^4.3.1",
  "cz-conventional-changelog": "^3.3.0"
},
"config": {
  "commitizen": {
  "path": "./node_modules/cz-conventional-changelog"
  }
}
```

- `scripts.cz`: run `npm run cz` as a shortcut
- `cz-conventional-changelog`: adapter for Conventional Commits
- `config.commitizen.path`: tells Commitizen which adapter to use