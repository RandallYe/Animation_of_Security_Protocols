This repository contains an animation Web UI implemented with [Yesod](https://www.yesodweb.com/). This repository is created using a template of Yesod. Refer to the [Yesod Quickstart guide](https://www.yesodweb.com/page/quickstart) for additional detail.

## Sound event trees

This web interface builds its stored event trees from the proved exploration of the Isabelle/HOL theories (see [Sec_Animation.thy](../User_Guided_Verification_Security/Sec_Animation.thy)). Each generated animator package now contains a `Sec_Animation.hs` that exports `explore`, `checks`, `feasible`, `reaches` and the check functions, and `explore_tree_NSPK3` / `explore_tree_NSLPK3` / `explore_tree_NSWJ3` / `explore_tree_DHWJ` build the tree from the traces of `explore` instead of the hand-written `explore_tree_cnt`: every stored node is a genuine trace, and every trace within the bounds is present. The proved `state_kind` oracle labels the leaves, so `Deadlocked`, `Terminated` and `Divergent` remain selectable events. Exploration bounds are now per protocol, every automatic check reports the bounds within which its verdict holds, and trees are built off the request path by a startup preload serialised on per-protocol locks, with a completion marker written in the same transaction as the rows so that an interrupted build is detected and redone. 

## Haskell Setup

1. If you haven't already, [install Stack](https://docs.haskellstack.org/en/stable/)
	* On POSIX systems, this is usually `$ curl -sSL https://get.haskellstack.org/ | sh`

2. Install the `yesod` command line tool: 

```
$ cd /path/to/animation-web-ui/
$ stack install yesod-bin --install-ghc
```

3. Build libraries: `stack build`

If you have trouble, refer to the [Yesod Quickstart guide](https://www.yesodweb.com/page/quickstart) for additional detail.

On Ubuntu, the following fixes were needed when `$ stack install yesod-bin --install-ghc` failed:

* `error: cannot find 'ld'` — install `binutils`, and force the use of `ld.bfd`, if there is no `ld.gold` here:

  ```
  $ sudo apt update
  $ sudo apt install binutils-gold
  ```

  Then retry step 2.
* Missing build dependencies — install them, then install `yesod-bin` with the system GHC:

  ```
  $ sudo apt-get update
  $ sudo apt-get install -y zlib1g-dev libtinfo-dev pkg-config
  $ stack --system-ghc install yesod-bin
  ```

## PlantUML Server
Clone the [PlantUML server](https://github.com/plantuml/plantuml-server) and run it:


```
$ git clone git@github.com:plantuml/plantuml-server.git
$ cd plantuml-server
$ sudo apt install maven
$ mvn jetty:run
```

Now the server is running locally, you can open [http://localhost:8080/plantuml/](http://localhost:8080/plantuml/) to check its status.

## Development

Start a development server with:


```
stack exec -- yesod devel
```

(If `yesod-bin` was installed with the system GHC, use `stack --system-ghc exec -- yesod devel` instead.)

As your code changes, your site will be automatically recompiled and redeployed to localhost.

Then type [http://localhost:3000](http://localhost:3000) in your browser to access the web interface.

## Tests

```
stack test --flag animation-web-ui:library-only --flag animation-web-ui:dev
```

(Because `yesod devel` passes the `library-only` and `dev` flags, matching those flags means you don't need to recompile between tests and development, and it disables optimization to speed up your test compile times).

## Deployment

```
stack build 
```
Then copy the binary file animate-web-ui to a folder which you want.

Then type [http://localhost:3000](http://localhost:3000) in your browser to access the web interface.
