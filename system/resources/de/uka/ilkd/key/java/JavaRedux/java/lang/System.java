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

//import java.io.*;
//import java.util.Properties;

/** JML's specification of java.lang.System.
 * Taken from jmlspecs repository (Java 1.4) and modified to fit to KeY.
 * @version $Revision: 2251 $ KeY
 * @author Gary T. Leavens
 * @author David R. Cok
 * @author Joseph R. Kiniry
 * @author Daniel Bruns
 */
public final class System {     


//    public final static java.io.InputStream in;
    public final static java.io.PrintStream out;
    public final static java.io.PrintStream err;
    
    


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
    public static native void arraycopy(/*@ nullable @*/ Object src,
                                        int srcPos,
                                        /*@ nullable @*/ Object dest,
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
