


package java.util;

import java.io.Serializable;
public class Random implements Serializable {
    public Random() {}
    public Random(long seed) {}
    public synchronized void setSeed(long seed) {}
    protected synchronized int next(int bits) {}
    public void nextBytes(byte[] bytes) {}
    public int nextInt() {}
    public int nextInt(int n) {}
    public long nextLong() {}
    public boolean nextBoolean() {}
    public float nextFloat() {}
    public double nextDouble() {}
    public synchronized double nextGaussian() {}
}
