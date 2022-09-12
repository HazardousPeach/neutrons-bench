# Static Analyzer Notes

## What's here?

 - Parser code
 - A simple database summary tool (summarize.sh)
 - Static analysis routines (analyze.sh)

## How do I use it?

 - run one of the shell scripts (summarize.sh or analyze.sh) with no arguments for help

Note that in order to build the tool, you'll need to `cabal install parsec syb`.

## Database summaries (summarize.sh)

Sample usage:

    $ ./summarize.sh ../therapyControl/opIOC

Prints information about what records are present in a DB, and how many of each there are. Sample output from Jon's code:

    Record types in use:
     213 ao
     175 ai
     156 calc
     109 calcout
      92 bo
      81 scalcout
      67 mbbo
      61 bi
      38 fanout
      37 seq
      23 stringin
      13 dfanout
      12 acalcout
      11 stringout
      10 subArray
       7 longout
       5 longin
       5 asyn
       3 waveform
