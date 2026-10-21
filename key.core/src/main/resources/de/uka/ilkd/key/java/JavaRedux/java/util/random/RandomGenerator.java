package java.util.random;

public interface RandomGenerator {

//    public static RandomGenerator of(String name);
//
//    public static RandomGenerator getDefault();

    public void setSeed(long seed);

    public boolean isDeprecated();

    public void nextBytes(byte[] bytes);

    public int nextInt();

    public int nextInt(int bound);

    public int nextInt(int origin, int bound);

    public long nextLong();

    public long nextLong(long bound);

    public long nextLong(long origin, long bound);

    public boolean nextBoolean();

    public float nextFloat();

    public float nextFloat(float bound);

    public float nextFloat(float origin, float bound);

    public double nextDouble();

    public double nextDouble(double bound);

    public double nextDouble(double origin, double bound);

    public double nextExponential();

    public double nextGaussian();

    public double nextGaussian(double mean, double stddev);

//   
//    public IntStream ints(long streamSize);
//
//    
//    public IntStream ints();
//
//    
//    public IntStream ints(long streamSize, int randomNumberOrigin, int randomNumberBound);
//
//    
//    public IntStream ints(int randomNumberOrigin, int randomNumberBound);
//
//    
//    public LongStream longs(long streamSize);
//
//    
//    public LongStream longs();
//
//    
//    public LongStream longs(long streamSize, long randomNumberOrigin, long randomNumberBound);
//
//    
//    public LongStream longs(long randomNumberOrigin, long randomNumberBound);
//    
//    public DoubleStream doubles(long streamSize);
//
//    
//    public DoubleStream doubles();
//
//    
//    public DoubleStream doubles(long streamSize, double randomNumberOrigin, double randomNumberBound);
//    
//    public DoubleStream doubles(double randomNumberOrigin, double randomNumberBound);
}