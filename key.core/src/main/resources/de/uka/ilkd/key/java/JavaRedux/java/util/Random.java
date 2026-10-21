package java.util;

public class Random implements java.util.random.RandomGenerator, java.io.Serializable {

    // @Override
    public void setSeed(long seed);

    // @Override
    public boolean isDeprecated();

    // @Override
    public void nextBytes(byte[] bytes);

    // @Override
    public int nextInt();

    public int nextInt(int bound);

    // @Override
    public int nextInt(int origin, int bound);

    // @Override
    public long nextLong();
    // @Override
    public long nextLong(long bound);

    // @Override
    public long nextLong(long origin, long bound);

    // @Override
    public boolean nextBoolean();

    // @Override
    public float nextFloat();

    // @Override
    public float nextFloat(float bound);

    // @Override
    public float nextFloat(float origin, float bound);

    // @Override
    public double nextDouble();

    // @Override
    public double nextDouble(double bound);

    // @Override
    public double nextDouble(double origin, double bound);

    // @Override
    public double nextExponential();

    // @Override
    public double nextGaussian();

    // @Override
    public double nextGaussian(double mean, double stddev);

//    // @Override
//    public IntStream ints(long streamSize);
//
//    // @Override
//    public IntStream ints();
//
//    // @Override
//    public IntStream ints(long streamSize, int randomNumberOrigin, int randomNumberBound);
//
//    // @Override
//    public IntStream ints(int randomNumberOrigin, int randomNumberBound);
//
//    // @Override
//    public LongStream longs(long streamSize);
//
//    // @Override
//    public LongStream longs();
//
//    // @Override
//    public LongStream longs(long streamSize, long randomNumberOrigin, long randomNumberBound);
//
//    // @Override
//    public LongStream longs(long randomNumberOrigin, long randomNumberBound);
//    // @Override
//    public DoubleStream doubles(long streamSize);
//
//    // @Override
//    public DoubleStream doubles();
//
//    // @Override
//    public DoubleStream doubles(long streamSize, double randomNumberOrigin, double randomNumberBound);
//    // @Override
//    public DoubleStream doubles(double randomNumberOrigin, double randomNumberBound);

    // @Override
    public String toString();
}