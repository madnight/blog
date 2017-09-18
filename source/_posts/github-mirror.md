---
title: Create Github Mirror
date: 2016-12-25
tags: ["Github", "Bash", "Programming"]
subtitle: Provide easy access to external repos via Github
---

# Motivation
Many big repositories are not hosted on Github, but do have a official mirror like linux[^1], git[^2] or ghc[^3]. The purpose of these mirrors is to provide an easy access (lower the barrier) to repositories that are not hosted on Github. There are many repositories that do not offer a official mirror.  Follow this short article, if you want to know how to create a mirror, to provide an easy access to external repositories as well.


# Clone
Step 0: Clone the repository you want to mirror
Step 1: Add your empty remote Github repository as origin

```sh
# example for valgrind
git svn clone svn://svn.valgrind.org/valgrind/trunk valgrind
cd valgrind
git remote add origin https://github.com/USERNAME/valgrind.git
```

# Mirror
Step 2: Create a `mirror.bash` file with all repositories you want to mirror and copy the contents below. Update the `GIT_PATH` and choose your mirrors.
```bash
while :
do
function update {
cd $GIT_PATH/$2

if [ $1 = "svn" ]; then
    git svn rebase upstream/master
else
    git rebase -s recursive -X theirs upstream/master
fi

git push -f origin master
}

update "svn" valgrind

# other examples
# update "git" grub
# update "git" nano
# update "svn" codeblocks

# repeat every 2 hours
sleep 2h
done
```

Step 3: Make the script executable `chmod x+u` and run it.

Example: [Valgrind mirror](https://github.com/madnight/valgrind)

## References
[^1]: [Mirror of the Linux Kernel](https://github.com/torvalds/linux)
[^2]: [Mirror of git](https://github.com/git/git)
[^3]: [Mirror of the Glasgow Haskell Compiler](https://github.com/ghc/ghc)
