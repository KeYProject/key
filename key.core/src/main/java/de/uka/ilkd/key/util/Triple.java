package de.uka.ilkd.key.util;


public class Triple<T1, T2, T3> {
    public final T1 first;
    public final T2 second;
    public final T3 third;


    public Triple(T1 first, T2 second, T3 third) {
        this.first = first;
        this.second = second;
        this.third = third;
    }


    public String toString() {
        return "(" + first + ", " + second + ", " + third + ")";
    }


    public boolean equals(Object o) {
        if (!(o instanceof Triple<?, ?, ?>)) {
            return false;
        }
        Triple<?, ?, ?> p = (Triple<?, ?, ?>) o;
        return (first == null ? p.first == null : first.equals(p.first))
                && (second == null ? p.second == null : second.equals(p.second))
                && (third == null ? p.third == null : third.equals(p.third));
    }


    public int hashCode() {
        int res = 0;
        if (first != null)
            res += 666 * first.hashCode();
        if (second != null)
            res += 42 * second.hashCode();
        if (third != null)
            res += 23 * third.hashCode();
        return res;
    }
}
