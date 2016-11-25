---
title: Create Github Mirror
date: 2016-12-25
tags: ["Github", "Bash", "Programming"]
cover: https://i.imgur.com/jhIkc55.jpg
---

## Clone
Step 1. Clone the repository you want to mirror
Step 2. Add your empty remote Github repository as origin

``` bash
# example for valgrind
git svn clone svn://svn.valgrind.org/valgrind/trunk valgrind
cd valgrind
git remote add origin https://github.com/USERNAME/valgrind.git
```
## Mirror
Step 3. Create a `mirror.bash` file with all repositories you want to mirror and copy the contents below. Update the `GIT_PATH` and choose your mirrors.
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
Step 4. Make the script executable `chmod x+u` and run it.

Example: [Valgrind mirror](https://github.com/madnight/valgrind)
