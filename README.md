#Penrose, a Petri Net reachability checker

##Authors

- Owen Stephens - owen@owenstephens.co.uk
- Pawel Sobocinski - ps@ecs.soton.ac.uk

##Installation

- Requires recent GHC and cabal to be installed.
    - Developed with GHC 7.6.3 and cabal 1.18.1.12
    - Tested with GHC 7.8.4 and cabal 1.22.0.0

1. run `cd PATH_TO_PENROSE_REPOSITORY`
2. run `cabal sandbox init`
3. run `cabal sandbox add-source mtbdd`
4. run `cabal install --only-dependencies --enable-tests --enable-benchmarks`
5. run `cabal configure && cabal build`


Penrose then exists as ./dist/build/Penrose/Penrose

##Usage

Penrose accepts net decompositions in the .netdecomp format. Several examples
are provided in the examples folder.

Usage:

```
./dist/build/Penrose/Penrose OUTPUT_TYPE PATH_TO_EXAMPLE
```

where the accepted values of OUTPUT_TYPE are shown by passing `--help` to Penrose

##Benchmarking

In-built benchmarking against punf/clp[1][2], cunf/cna[3], LOLA[4], MARCIE[5] and TAPAAL[6] are
enabled by passing the `--enable-benchmarks` flag to cabal configure in step 6.  above.

A yet-to-be-diagnosed stack overflow occurs when running the benchmarks, so the
Haskell run time system must be instructed to allow larger stacks. This is
done when running the benchmarks as follows:

```
./dist/build/Benchmark/Benchmark TYPE [Benchmark] +RTS -K200M
```

which instructs the Haskell RTS to use 200M of stack, which is sufficient.
Pass --help to Benchmark to see the flags for TYPE. An optional sequence of
benchmark names can be passed, to restrict which benchmarks are run. E.g. to
run LOLA on the buffer and philo examples, run:

```
./dist/build/Benchmark/Benchmark LOLA buffer philo +RTS -K200M
```

Or to run Penrose (available without installing other tools):

```
./dist/build/Benchmark/Benchmark PENROSE buffer philo 
```

[1]: http://homepages.cs.ncl.ac.uk/victor.khomenko/home.formal/tools/punf/
[2]: http://homepages.cs.ncl.ac.uk/victor.khomenko/tools/clp/
[3]: https://code.google.com/p/cunf/
[4]: http://download.gna.org/service-tech/lola/
[5]: http://www-dssz.informatik.tu-cottbus.de/DSSZ/Software/Marcie
[6]: http://www.tapaal.net/
