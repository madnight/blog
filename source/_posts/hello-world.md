---
title: Create Github Mirror
---

Clone the repository you want to mirror and ..

``` bash
function update {
cd ~/Git/$2
if [ $1 = "svn" ]; then
  git svn rebase upstream/master
else
  git rebase -s recursive -X theirs upstream/master
fi
git push -f origin master
}

  update "git" MetaGer
  update "git" scid
  update "git" sed
  update "git" gnupg
  update "git" grub
  update "git" nano

  update "svn" lfs
  update "svn" filezilla
  update "svn" gnuchess
  update "svn" valgrind
  update "svn" scidvspc
  update "svn" chessx
  update "svn" codeblocks
```

More info: [Writing](https://hexo.io/docs/writing.html)

### Run server

``` bash
$ hexo server
```

More info: [Server](https://hexo.io/docs/server.html)

### Generate static files

``` bash
$ hexo generate
```

More info: [Generating](https://hexo.io/docs/generating.html)

### Deploy to remote sites

``` bash
$ hexo deploy
```

More info: [Deployment](https://hexo.io/docs/deployment.html)
