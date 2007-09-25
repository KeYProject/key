package java.util;

public interface Map
{

    //@ public model instance non_null JMLEqualsSet theMap;
    //@ instance ghost public boolean containsNull;
    //@ public instance ghost Object[][] concrete_map;

    /*@ public instance invariant
      @  (\forall int i; i>=0 && i<concrete_map.length; 
      @   concrete_map[i].length == 2) &&
      @  \nonnullelements(concrete_map) && 
      @  (\forall int i,j; concrete_map[j][0]==concrete_map[i][0]; i==j);
      @*/   

    /*@ public instance invariant  
      @      (\forall Object o; theMap.has(o); o instanceof java.util.Map.Entry);
      @*/
	   
    /*@ public instance invariant 	   
      @      (\forall Object o1, o2; theMap.has(o1) && theMap.has(o2); 
      @                             o2!=o1 ==> !JMLNullSafe.equals(o2,o1));
      @*/

    /*@ public normal_behavior
      @    assignable theMap;
      @       ensures theMap.isEmpty();
      @*/
  void clear();

    /*@ public normal_behavior
      @    requires key != null;
      @    ensures \result <==>
      @      (\exists java.util.Map.Entry e; theMap.has(e) && e != null; 
      @                            JMLNullSafe.equals(e.abstractKey, key));
      @  also 
      @ public normal_behavior
      @    requires key != null;
      @    ensures \result <==> (\exists int i; i>=0 && i<size(); 
      @                          concrete_map[i][0].equals(key));
      @*/
    /*@ pure @*/
  boolean containsKey(Object key);

    /*@ public behavior
      @    ensures \result <==>
      @      (\exists java.util.Map.Entry e; theMap.has(e) && e != null; 
      @                            JMLNullSafe.equals(e.abstractValue, value));
      @    signals (ClassCastException)
      @         (* if the value is not appropriate for this object *);
      @    signals (NullPointerException) value == null
      @         && (* this type doesn't permit null values *);
      @*/
  boolean /*@ pure @*/ containsValue(Object value);

    /*@ public normal_behavior
      @    ensures \result != null && \result.theSet.equals(theMap);
      @*/
    /*@ pure @*/
  Set entrySet();

  boolean /*@ pure @*/ equals(Object o);

    /*@ public normal_behavior
      @    requires !containsKey(key);
      @    ensures \result == null;
      @  also
      @ public normal_behavior
      @    requires containsKey(key);    
      @    ensures (\exists java.util.Map.Entry e; theMap.has(e); e != null
      @            && JMLNullSafe.equals(e.abstractKey, key)
      @            && \result.equals(e.abstractValue));
      @  also
      @ public normal_behavior
      @    requires (\exists int i; i>=0 && i<concrete_map.length; 
      @              concrete_map[i][0]==key);
      @    ensures  (\exists int i; i>=0 && i<concrete_map.length; 
      @              concrete_map[i][0]==key && \result == concrete_map[i][1]);
      @*/
  Object /*@ pure @*/ get(Object key);

    /*@ public behavior
      @    assignable theMap;
      @    ensures (\exists java.util.Map.Entry e; theMap.has(e); e != null
      @            && JMLNullSafe.equals(e.abstractKey, key)
      @            && JMLNullSafe.equals(e.abstractValue, value)
      @            && \result.equals(\old(e.abstractValue)));
      @    signals (NullPointerException) \not_modified(value)
      @             && (key==null)||(value==null) && !containsNull;
      @    signals (UnsupportedOperationException) \not_modified(theMap) 
      @             && (* if the map's put operation is not supported  *);
      @    signals (ClassCastException) \not_modified(theMap)
      @             && (* \typeof(key) or \typeof(value) is incompatible
      @                with the valueType or keyType of this map *);
      @    signals (IllegalArgumentException) \not_modified(theMap)
      @             && (* if some aspect of key or value is not 
      @                allowed in the map *);
      @*/
  Object put(Object key, Object value);

  int /*@ pure @*/ hashCode();

    /*@ public normal_behavior
      @    ensures \result <==> theMap.isEmpty(); 
      @*/
  boolean isEmpty();

    /*@ public normal_behavior 
      @    ensures \result != null
      @      && (\forall Object k; containsKey(k); \result.contains(k))
      @      && (\forall Object k; \result.contains(k); containsKey(k));
      @*/
  Set /*@ pure @*/ keySet();

    /*@ public behavior
      @    assignable theMap;
      @    ensures (\forall java.util.Map.Entry e; t.theMap.has(e); 
      @                              theMap.has(e));
      @    signals (NullPointerException) \not_modified(theMap)
      @             && (t == null) && !containsNull;
      @    signals (UnsupportedOperationException) \not_modified(theMap) 
      @             && (* if the map's put operation is not supported  *);
      @    signals (ClassCastException) \not_modified(theMap)
      @             && (* \typeof(t) or is incompatible
      @                with this map *);
      @    signals (IllegalArgumentException) \not_modified(theMap)
      @             && (* if some aspect of a key or value is not 
      @                allowed in the map *);
      @*/
  void putAll(Map t);

    /*@ public behavior
      @    assignable theMap;
      @    ensures \result != null
      @        ==> (\exists java.util.Map.Entry e; e != null && \old(theMap.has(e));
      @                      JMLNullSafe.equals(e.abstractKey, key)
      @                   && \result.equals(e.abstractValue)); 
      @    ensures !(\exists java.util.Map.Entry e; e != null && \old(theMap.has(e));
      @                      JMLNullSafe.equals(e.abstractKey, key));
      @    signals (UnsupportedOperationException)
      @              (* if this operation is not supported *);
      @    signals (ClassCastException)
      @              (* if the argument is not appropriate *);
      @    signals (NullPointerException) key == null
      @              && (* if this map doesn't support null keys *);
      @*/
  Object remove(Object key);

  int size();

    /*@ public normal_behavior 
      @    ensures \result != null
      @      && (\forall Object v; containsValue(v); \result.contains(v))
      @      && (\forall Object v; \result.contains(v); containsValue(v));
      @*/
  /*@ pure @*/
  Collection values();

    /*@ also 
      @  public normal_behavior
      @    requires o instanceof Map;
      @    ensures \result <==> theMap.equals(o);
      @ also
      @  public normal_behavior
      @    requires !(o instanceof Map);
      @    ensures \result == false;
      @*/
    /*@ pure @*/ boolean equals(Object o);

  interface Entry
  {
      //@ public model instance Object abstractKey;
      //@ public model instance Object abstractValue;
      //@ ghost public boolean containsNull;

      /*@  public normal_behavior
	@     ensures \result.equals(abstractKey);
	@*/
    Object getKey();

      /*@  public normal_behavior
	@     ensures \result.equals(abstractValue);
	@*/
    Object getValue();

        /*@  public behavior
          @     assignable this.abstractValue;
          @     ensures JMLNullSafe.equals(\result, \old(this.abstractValue))
          @          && JMLNullSafe.equals(value, this.abstractValue);
          @     signals (NullPointerException) \not_modified(this.abstractValue)
          @             && (abstractValue == null) && !containsNull;
          @     signals (UnsupportedOperationException)
          @               \not_modified(this.abstractValue) 
          @             && (* if the map's put operation is not supported  *);
          @     signals (ClassCastException) \not_modified(this.abstractValue)
          @             && (* \typeof(abstractValue) is incompatible
          @                with the valueType of this map *);
          @     signals (IllegalArgumentException) \not_modified(this.abstractValue)
          @             && (* if some aspect of value is not 
          @                allowed in the map *);
          @*/
    Object setValue(Object value);

    /*@ pure @*/
    int hashCode();

        /*@  also
          @   public normal_behavior
          @     requires o instanceof Entry;
          @     ensures \result == 
          @      (    JMLNullSafe.equals(((Entry)o).abstractKey, abstractKey)
          @        && JMLNullSafe.equals(((Entry)o).abstractValue,
          @                              abstractValue) );
          @  also
          @   public normal_behavior
          @     requires !(o instanceof Entry);
          @     ensures \result == false;
          @*/
    boolean equals(Object o);
  }
}
