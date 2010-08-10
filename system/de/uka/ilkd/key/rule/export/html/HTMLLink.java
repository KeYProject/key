// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.rule.export.html;



public abstract class HTMLLink {
    public String openingTag () {
        return "<a href=\"" + getURL () + "\">";
    }
    
    public String closingTag () {
        return "</a>";
    }
    
    public String toTag ( Object o ) {
        return openingTag() + o + closingTag();
    }
    
    protected abstract String getURL ();
}
