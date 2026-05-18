/*
 * Copyright (c) 2015, 2025, Oracle and/or its affiliates. All rights reserved.
 * ...
 */
package micro.benchmarks;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Mode;
import org.openjdk.jmh.annotations.OutputTimeUnit;
import org.openjdk.jmh.annotations.Param;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.State;

import java.util.concurrent.TimeUnit;

@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Thread)
public class NonlinearIVBenchmark extends BenchmarkBase {

    @Param({"1000", "100000", "1000000"})
    public int n;

    public static int loop(int n) {
        int i, j, k;
        j = 0;
        k = 0;
        for (i = 0; i < n; i++) {
            j = i * 13;
            k = k - 1;
        }
        return j + k;
    }

    @Benchmark
    public int testLoop() {
        return loop(n);
    }
}