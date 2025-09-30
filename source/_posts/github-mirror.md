---
title: Create a GitHub Mirror
date: 2016-12-25
tags: ["github", "bash", "programming"]
subtitle: Provide easy access to external repos via GitHub
categories:
  - Computer Science
---

# Motivation
Many big repositories are not hosted on GitHub, but do have a official mirror like [linux](https://github.com/torvalds/linux), [git](https://github.com/git/git) or [ghc](https://github.com/ghc/ghc). The purpose of these mirrors is to provide an easy access (lower the barrier) to repositories that are not hosted on GitHub. There are many repositories that do not offer a official mirror.  Follow this short article, if you want to know how to create a mirror, to provide an easy access to external repositories as well.

# Clone
**Step 0:** Clone the repository you want to mirror.
**Step 1:** Add your empty remote GitHub repository as mirror.

{% vimhl py %}
# example for valgrind
git svn clone svn://svn.valgrind.org/valgrind/trunk valgrind
cd valgrind
git remote add mirror https://github.com/USERNAME/valgrind.git
{% endvimhl %}

# Mirror
**Step 2:** Create a `mirror.bash` file with all repositories you want to mirror and copy the contents below. Update the `GIT_PATH` and choose your mirrors.
{% vimhl bash %}
while :
do
function update {
cd $GIT_PATH/$2

if [ $1 = "svn" ]; then
    git svn rebase origin/master
else
    git rebase -s recursive -X theirs origin/master
fi

git push -f mirror master
}

update "svn" valgrind

# other examples
# update "git" grub
# update "git" nano
# update "svn" codeblocks

# repeat every 2 hours
sleep 2h
done
{% endvimhl %}

**Step 3:** Make the script executable `chmod x+u` and run it. Example: [Valgrind mirror](https://github.com/madnight/valgrind)


