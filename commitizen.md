# Code Submission with `git cz` (Commitizen)

Use Commitizen to replace `git commit` with an interactive, standardized commit flow that follows the Conventional Commits spec.

---

## Require
- [node](https://nodejs.org/en/) >= 10

## Quick Start

```bash
# 0) prerequisites
# Make sure you have git and Node.js/npm installed
# Ubuntu: 
sudo apt install npm

# 1) initialize Node context in your repo root
cd /YOUR-PATH/this-repo
npm init -y

# 2) install Commitizen + adapter
npm install --save-dev commitizen

# 3) write Commitizen to the adapter
npx commitizen init cz-conventional-changelog --save-dev --save-exact

# 4) add a convenient script to the `scripts` field of `package.json`
#  "scripts": { 
#     ...
#     "cz": "git-cz"
#  }
```

Then, you can use `npm run cz` or `git cz` (where PATH contain node_modules/.bin) to commit your code

If you want to use `git cz` globally (where PATH not contain node_modules/.bin), you can run
```shell
$ npm install -g commitizen
```
Then, you can use `git cz` to commit your code in terminal globally.

## Usage
- When ready to commit changes, instead of `git commit`, use `git cz` or `npm run cz`.
- git cz will prompt you to select the type of commit (e.g., feat, fix, docs, style, refactor, test).
- Enter a scope, and enter a short, descriptive title for the commit. For example, Add user login function.
- Optionally provide a detailed description of the changes.

For example:

```bash
git add -A
npm run cz
# then push as usual
git push
```

---
