
# Problem

[Dining Philosophers Problem](https://en.wikipedia.org/wiki/Dining_philosophers_problem)

# How to run

```
export CLASSPATH=`location of tla2tools.jar`/*

java pcal.trans dining_deadlock.tla
java tlc2.TLC ./dining_deadlock.tla

java pcal.trans dining_no_deadlock.tla
java tlc2.TLC ./dining_no_deadlock.tla
```



