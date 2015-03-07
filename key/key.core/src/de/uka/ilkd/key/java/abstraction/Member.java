// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.abstraction;

/**
   A program model element representing members.   
 */
public interface Member extends ProgramModelElement {

    /**
       Checks if this member is final.
       @return <CODE>true</CODE> if this member is final,
       <CODE>false</CODE> otherwise.
     */
    boolean isFinal();
    
    /**
       Checks if this member is static. Returns <CODE>true</CODE>
       for {@link recoder.abstraction.Constructor}s.
       @return <CODE>true</CODE> if this member is static,
       <CODE>false</CODE> otherwise.
     */
    boolean isStatic();
    
    /**
       Checks if this member is private.
       @return <CODE>true</CODE> if this member is private,
       <CODE>false</CODE> otherwise.
     */
    boolean isPrivate();
    
    /**
       Checks if this member is protected.
       @return <CODE>true</CODE> if this member is protected,
       <CODE>false</CODE> otherwise.
     */
    boolean isProtected();
    
    /**
       Checks if this member is public.
       @return <CODE>true</CODE> if this member is public,
       <CODE>false</CODE> otherwise.
     */
    boolean isPublic();
    
    /**
       Checks if this member is strictfp.
       @return <CODE>true</CODE> if this member is strictfp,
       <CODE>false</CODE> otherwise.
     */
    boolean isStrictFp();
}