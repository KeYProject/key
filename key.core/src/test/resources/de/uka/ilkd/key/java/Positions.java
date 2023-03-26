// Does nothing sensible. This file is used by TestPositions to validate positions in the source code
// If new problems arise, this file can be extended (best appended) to cover more cases.
package qwe.rty;

import qwe.rty.A;

@SomeAnnotation(integer = 5, string = "Hi")
public abstract class A extends Inner implements Z {
    static {
        d = 3;
        @SomeAnnotation(integer = 5, string = "Hi")
        Object v = new Object();
    }

    @SomeAnnotation(integer = 5, string = "Hi")
    public static int d;
    long f;
    String st;

    @Override
    @SomeAnnotation(integer = 5, string = "Hi")
    public String toString();

    public void abc(int j, long k, String str) throws Exception {
        Object z = new A(4, 5) {
            public int d = 7;
        };
        abc();
        A a = (A) null;
        a = def(a);
        a = def(a).ghi(a).ghi(a);
        throw new Exception();
    }

    public <T> void test() {
        {
            int j = 7;
            int i;
            i = 1;
            byte d = 0;
            short f = 1;
            long l = 123;
            for (i = 0, j = 1; (i < 42) && (i > 0); i++, j--) {
                i = 13;
                j = 1;
            }
            while ((-i < 7) || (i++ == 7--) | (--i == ++7) || (!true && false) || ('a' == 'd')
                    || ("asd" == "as" + "d") & (d == f) ^ (d / f + 2 >= f * d - f % d) || (l <= ~i)
                    || !(this == null) || ((this != null) ? (8 << j < 8 >> i) : (7 & 5 > 8 >>> 7L)
                    || (7 | 5 != 8 ^ 4)) && i += j && i = j && i /= j && i %= j && i -= j && i *= j
                    && i <<= j && i >>= j && i >>>= j && i &= j && i ^= j && i |= j) j = 7;
        }
        {
            int j = 7;
            int i;
            i = 1;
            do {
                j++;
            } while (i == 1);
            if (j == 42) j = 7;
            else {
                i = 7;
                j = 43;
            }
            label0:
            j = 42;
            switch (j - i) {
                case 7:
                    j = 2;
                case 42:
                    j = 3;
                default:
                    j = 4;
            }
            while (j == 42) loop1:{
                if (j == 7) break;
                if (j == 43) break loop1;
                if (j == 42) continue;
                if (j == 41) continue loop1;
            }
            if (j > 42) return;
            synchronized (null) {
                j = 7;
            }
        }
        {
            int x = 1;
            {
                float l;
            }
        }
        {
            int[] a;
            a = new int[3];
            a = new int[]{2, 3, 4};
            a[1] = 0;
            int[][] b;
            a = new int[3][2];
            a[0][0] = 10;
            int j = a[2];
            j = a.length;
        }
    }
}

class Inner {

}

@SomeAnnotation(integer = 5, string = "Hi")
interface Z0 {

}

interface Z extends Z0 {
    public int d = 100;
}

class Parameterized<T, U extends Z> {
    T value;
}