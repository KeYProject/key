// Copyright (C) 1998-2006 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.lang;

import java.io.*;
import java.util.Properties;

/** JML's specification of java.lang.System.
 *
 * @version $Revision: 2251 $ KeY
 * @author Gary T. Leavens
 * @author David R. Cok
 * @author Joseph R. Kiniry
 * @author Daniel Bruns
 */
public final /*@ nullable_by_default @*/ class System {

    //@ public final ghost static boolean allowNullStreams = false;

    /*  In declaring allowNullStreams to be final, we restrict beyond what
        the JDK requires.  The JDK allows in, out and err to be set to null
        streams, in which case a NullPointerException is raised on any
        attempt to read or write to in, out or err.  By declaring 
        allowNullStreams final we introduce the invariant that it is always
        non-null.  If we don't do this, we will need to include in preconditions
        whereever in, out and err are used that they are non null.  This is
        a decided nuisance, and I think the programmer would rather be
        warned that a possibly null stream is being assigned. 

	Since allowNullStreams = false and is declared as final, this means
	that in, out and err are effectively non-null.  The only way to allow
	them to be nullable is to modify this specification (or make a copy of
	it) and change the value of allowNullStreams.  Since changing the
	nullity requires changing the spec, and since some tools can do more
	if in, out and err are explicitly declared non-null, we are going one
	step further and annotating in, out and err as non_null.  If ever you
	change allowNullStreams to be true, then you will need to change the
	annotations of in, out and err to be nullable.
    */

//    public final static /*@non_null*//*see note above*/ InputStream in;
//    public final static /*@non_null*//*see note above*/ PrintStream out;
//    public final static /*@non_null*//*see note above*/ PrintStream err;

    /* @ requires allowNullStreams || i != null;
      @ assignable in;  // strangely enough, in is like a read-only var.
      @ ensures in == i;
      @*/
//    public static void setIn(InputStream i);

    /* @ requires allowNullStreams || o != null;
      @ assignable out;
      @ ensures out == o;
      @*/
//    public static void setOut(PrintStream o);

    /* @ requires allowNullStreams || e != null;
      @ assignable err;
      @ ensures err == e;
      @*/
//    public static void setErr(PrintStream e);


    // @ public model static nullable SecurityManager systemSecurityManager;

    /* @  public normal_behavior
      @    requires s == null;
      @    assignable \nothing;
      @    ensures \not_modified(systemSecurityManager);
      @ also
      @  public behavior
      @    requires s != null;
      @    assignable systemSecurityManager;
      @    ensures  systemSecurityManager == s;
      @    signals (SecurityException) (* if the change is not permitted *);
      @*/
//    public static void setSecurityManager(/*@nullable*/ SecurityManager s) throws SecurityException;

    /* @ public normal_behavior
      @   ensures \result == systemSecurityManager;
      @*/
//    public /*@ pure @*/ static /*@nullable*/ SecurityManager getSecurityManager();

    /** The last value of currentTimeMillis() that was returned */

    //@ public static ghost long time;

    // FIXME - need to show that the value is volatile ?
    //@ public normal_behavior
    //@  modifies time;
    //@  ensures \result >= 0;
    //@  ensures time >= \old(time);
    //@  ensures \result == time;
    public static native long currentTimeMillis();

    /*@ public exceptional_behavior
      @   requires src == null || dest == null;
      @   assignable \nothing;
      @   signals_only NullPointerException;
      @ also
      @  public behavior
      @    requires !(src == null || dest == null);
      @    requires !(    srcPos < 0 || destPos < 0 || length < 0 );
             // FIXME - need the length restrictions for all primitive types
	   {| requires src instanceof Object[] &&
		         dest instanceof Object[] &&
      @                 srcPos + length <= ((Object[])src).length
      @                && destPos + length <= ((Object[])dest).length;
      @   {|
      @      assignable ((Object[])dest)[destPos .. destPos + length - 1];
      @      ensures (\forall int i; 0 <= i && i < length;
      @                \old(((Object[])src)[(int)(srcPos+i)]) == ((Object[])dest)[(int)(destPos+i)]);
      @   |}
	   also
		requires src instanceof int[] &&
			 dest instanceof int[] &&
      @                 srcPos + length <= ((int[])src).length
      @                && destPos + length <= ((int[])dest).length;
      @   {|
      @      assignable ((int[])dest)[destPos .. destPos + length - 1];
      @      ensures (\forall int i; 0 <= i && i < length;
      @                 ((int[])src)[(int)(srcPos+i)] == ((int[])dest)[(int)(destPos+i)]);
      @   |}
	   also
		requires src instanceof long[] &&
			 dest instanceof long[] &&
      @                 srcPos + length <= ((long[])src).length
      @                && destPos + length <= ((long[])dest).length;
      @   {|
      @      assignable ((long[])dest)[destPos .. destPos + length - 1];
      @      ensures (\forall int i; 0 <= i && i < length;
      @                 ((long[])src)[(int)(srcPos+i)] == ((long[])dest)[(int)(destPos+i)]);
      @   |}
      @ also
      @   signals_only ArrayStoreException, ArrayIndexOutOfBoundsException;
	   |}
      @*/
    public static native void arraycopy(/*@non_null*/ Object src,
                                        int srcPos,
                                        /*@non_null*/ Object dest,
                                        int destPos,
                                        int length);

    // Note: Unequal objects are not required to have unequal hashCodes
    // There is no good, modularly provable way to express that anyway
    //@ public normal_behavior
    //@   ensures x == null ==> \result == 0;
    public /*@ pure @*/ static native int identityHashCode(/*@nullable*/ Object x);


    /*@ public behavior
      @    diverges true;
      @    assignable \nothing;
      @    ensures false;
      @*/
    public static void exit(int status);

    public static void gc();

    public static void runFinalization();

    /** @deprecated this is unsafe. */
    public static void runFinalizersOnExit(boolean value);

    public static void load(/*@ non_null @*/ String filename);

    public static void loadLibrary(/*@ non_null @*/ String libname);

    public /*@ pure @*/ static native String mapLibraryName(/*@non_null*/ String libname);

}
