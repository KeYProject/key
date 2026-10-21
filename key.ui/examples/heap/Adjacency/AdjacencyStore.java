/**
 * Storing one node's neighbour list into the flat edge array of an adjacency structure.
 */
public final class AdjacencyStore {

    /*@ public normal_behavior
      @ requires edges != null && list != null && edges != list;
      @ requires 0 <= at && 0 <= n;
      @ requires at + n <= edges.length;
      @ requires n <= list.length;
      @ ensures (\forall int i; 0 <= i && i < n; edges[at + i] == list[i]);
      @ assignable edges[at .. at + n - 1];
      @*/
    public static void storeList(int[] edges, int at, int[] list, int n) {
        int i = 0;
        /*@ loop_invariant 0 <= i && i <= n;
          @ loop_invariant (\forall int t; 0 <= t && t < i; edges[at + t] == list[t]);
          @ assignable edges[at .. at + n - 1];
          @ decreases n - i;
          @*/
        while (i < n) {
            edges[at + i] = list[i];
            i++;
        }
    }

    /*@ public normal_behavior
      @ requires edges != null && list != null && edges != list;
      @ requires 0 <= at && 0 <= n;
      @ requires at + n <= edges.length;
      @ requires n <= list.length;
      @ requires (\forall int i; 0 <= i && i < n; 0 <= list[i] && list[i] < nodeCount);
      @ ensures (\forall int p; at <= p && p < at + n;
      @              0 <= edges[p] && edges[p] < nodeCount);
      @ assignable edges[at .. at + n - 1];
      @*/
    public static void storeValidList(int[] edges, int at, int[] list, int n, int nodeCount) {
        storeList(edges, at, list, n);
    }

    /*@ public normal_behavior
      @ requires edges != null && list != null && edges != list;
      @ requires 0 <= at && 0 <= n;
      @ requires at + n <= edges.length;
      @ requires n <= list.length;
      @ requires (\forall int u, v; 0 <= u && u < v && v < n; list[u] != list[v]);
      @ ensures (\forall int p, q; at <= p && p < q && q < at + n; edges[p] != edges[q]);
      @ assignable edges[at .. at + n - 1];
      @*/
    public static void storeDistinctList(int[] edges, int at, int[] list, int n) {
        storeList(edges, at, list, n);
    }
}
