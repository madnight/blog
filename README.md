# Personal Blog
[![](https://travis-ci.org/madnight/docker-alpine-wkhtmltopdf.svg)](https://travis-ci.org/madnight/docker-alpine-wkhtmltopdf)

based on https://hexo.io


### Theme
Customized Beautiful Hexo
https://github.com/twoyao/beautiful-hexo

### Install
```bash
yarn global add hexo-cli
yarn install
```

### Develop
```bash
hexo clean && hexo generate && hexo server
```

### Deploy
The blog is auto deployed via travis-ci on push to master.

Manual deploy goes as follows.
```bash
# build and deploy to gh-pages branch
hexo clean && hexo deploy --generate
```

https://hexo.io/docs/deployment.html
