package sourcerer.util;

import recoder.ModelElement;
import recoder.NamedModelElement;
import recoder.ServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.ClassTypeContainer;
import recoder.abstraction.Constructor;
import recoder.abstraction.Field;
import recoder.abstraction.Member;
import recoder.abstraction.Method;
import recoder.abstraction.Package;
import recoder.abstraction.ProgramModelElement;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.TypeDeclaration;
import recoder.service.NameInfo;

/**
   Auxiliaries for source code works.
 */
public class RecoderUtils {
    /**
       Returns the next program element in the depth first order of the
       syntax tree, or <CODE>null</CODE> if there is no successor.
       If start positions are valid, the returned element will have a 
       higher starting position than the given one.
       @param p a program element to find the successor for.
       @return the successor of the given element.
     */
    public static ProgramElement getNextInSource(ProgramElement p) {
	if (p instanceof NonTerminalProgramElement) {
	    if (((NonTerminalProgramElement)p).getChildCount() > 0) {
		return ((NonTerminalProgramElement)p).getChildAt(0);
	    }
	}
	return getNextOnLevel(p);
    }

    /**
       Returns the next program element of the current depth level in the
       syntax tree, or <CODE>null</CODE> if there is no successor.
       If a node is the last sibling of a non terminal, the next node
       in the depth first order will be reported (the next avaiable cousin, or
       grand cousin, or grand-grand-cousin and so on).
       @param p a program element.
       @return the successor of the given element on the same level.
     */
    public static ProgramElement getNextOnLevel(ProgramElement p) {
	NonTerminalProgramElement parent = p.getASTParent();
	while (parent != null) {
	    int pos = parent.getIndexOfChild(p) + 1;
	    if (pos < parent.getChildCount()) {
		return parent.getChildAt(pos);
	    }
	    p = parent;
	    parent = parent.getASTParent();
	}
	return null;
    }

    public static ProgramElement getPreviousInSource(ProgramElement p) {
	NonTerminalProgramElement parent = p.getASTParent();
	if (parent != null) {
	    int pos = parent.getIndexOfChild(p) - 1;
	    if (pos >= 0) {
		p = parent.getChildAt(pos);
		while (p instanceof NonTerminalProgramElement) {
		    int cc = ((NonTerminalProgramElement)p).getChildCount();
		    if (cc == 0) {
			break;
		    }			    
		    p = ((NonTerminalProgramElement)p).getChildAt(cc - 1);
		}
		return p;
	    }
	}
	return parent;
    }

    public static ProgramElement getPreviousOnLevel(ProgramElement p) {
	NonTerminalProgramElement parent = p.getASTParent();
	if (parent != null) {
	    int pos = parent.getIndexOfChild(p) - 1;
	    if (pos >= 0) {
		p = parent.getChildAt(pos);
		return p;
	    } else {
		return parent;
	    }
	}
	return null;
    }

    // returns the element that surrounds the given position
    // returns the root element for external positions
    public static ProgramElement getElementAtPosition(ProgramElement root, int line, int column) {
	ProgramElement nearest = root;
	TreeWalker w = new TreeWalker(root);
	while (w.next()) {
	    ProgramElement p = w.getProgramElement();
	    Position spos = p.getFirstElement().getStartPosition();
	    if (spos.getLine() > line) {
		break;
	    }
	    if (spos.getLine() == line && spos.getColumn() > column) {
		break;
	    }
	    Position epos = p.getLastElement().getEndPosition();
	    if (epos.getLine() > line || (epos.getLine() == line && epos.getColumn() >= column)) {
		nearest = p;
	    }
	}
	return nearest;	
    }
    
    // works for program elements and program model elements only
    public static boolean isModelPart(ServiceConfiguration sc, ModelElement p) {
	if (p instanceof ProgramElement) {
	    return isModelPart(sc, (ProgramElement)p);
	}
	if (p instanceof ProgramModelElement) {
	    return isModelPart(sc, (ProgramModelElement)p);
	}
	return false;
    }

    public static boolean isModelPart(ServiceConfiguration sc, ProgramElement p) {
	while (true) {
	    NonTerminalProgramElement parent = p.getASTParent();
	    if (parent == null) {
		if (p instanceof CompilationUnit) {
		    return sc.getSourceFileRepository().getKnownCompilationUnits().indexOf(p) >= 0;
		} else {
		    return false;
		}
	    }
	    if (parent.getIndexOfChild(p) == -1) {
		return false; // has been detached
	    }
	    p = parent;
	}
    }

    /**
      Checks if the given program model element is part of the model
      or has been removed or replaced.
     */
    public static boolean isModelPart(ServiceConfiguration sc,
				      ProgramModelElement pme) {
	if (pme instanceof ProgramElement) {
	    return isModelPart(sc, (ProgramElement)pme);
	}
	NameInfo ni = sc.getNameInfo();
	if (pme instanceof Package) {
	    return (ni.getPackage(pme.getFullName()) == pme);
	}
	if (pme instanceof Type) {
	    // handle primitive types, array types and top level classes
	    if (!(pme instanceof ClassType) || (((ClassType)pme).getContainer() instanceof Package)) {
		return (ni.getType(pme.getFullName()) == pme);
	    }
	}
	if (pme instanceof Member) {
	    ClassType parent = ((Member)pme).getContainingClassType();
	    if (pme instanceof Constructor) {
		return parent.getConstructors().indexOf(pme) >= 0 &&
		    isModelPart(sc, parent);
	    }
    // for default constructors, check if the container
    // has no constructor declarations AND is valid.
	    if (pme instanceof Method) {
		return parent.getMethods().indexOf(pme) >= 0 &&
		    isModelPart(sc, parent);
	    }
	    if (pme instanceof Field) {
		return parent.getFields().indexOf(pme) >= 0 &&
		    isModelPart(sc, parent);
	    }
	    if (pme instanceof ClassType) {
		return parent.getTypes().indexOf(pme) >= 0 &&
		    isModelPart(sc, parent);
	    }
	}
	// should not be here; variables are covered by program elements
	return false;	
    }


    // returns the logical container of the given program model element
    // for fields or methods or constructors, reports class type,
    // for class types, reports enclosing class type or package
    public static ClassTypeContainer getContainer(ProgramModelElement p) {
	ClassTypeContainer con = null;
	if (p instanceof Member) {
	    con = ((Member)p).getContainingClassType();
	}
	if ((con == null) && (p instanceof ClassTypeContainer)) {
	    con = ((ClassTypeContainer)p).getContainer();
	}
	return con;
    }

    // returns a top-level program model element associated with the s
    // pecified program element.
    // if the program element is a top-level program model element, it is 
    // returned
    // if it is contained in a program model element, that element is returned
    // else the package of the compilation unit is returned
    // null is returned in any other cases (unrooted syntax trees)
    public static ProgramModelElement getAssociatedProgramModelElement(ProgramElement p) {
	do {
	    if (p instanceof ProgramModelElement) {
		if (!(p instanceof Variable) || p instanceof Field) {
		    return (ProgramModelElement)p;
		}
	    }
	    if (p instanceof CompilationUnit) {
		p = ((CompilationUnit)p).getPrimaryTypeDeclaration();
		if (p == null) {
		    return null;
		}		
		return ((ClassType)p).getPackage();
	    }
	    p = p.getASTParent();
	} while (p != null);
	return null;
    }

    public static String getShortName(Package p) {
	String res = p.getName();
	return res.substring(res.lastIndexOf('.') + 1);	    
    }

    public static String getShortName(CompilationUnit cu) {
	TypeDeclaration pt = cu.getPrimaryTypeDeclaration();
	return (pt == null) ? "" : pt.getName();
    }	

    /**
       Returns the (short) name of the specified element,
       replacing the name of anonymous types and the default package.
     */
    public static String getNonTrivialName(NamedModelElement m) {
	String name = m.getName();
	if (name == null || name.length() == 0) {
	    if (m instanceof ClassType) {
		name = "(Anonymous Type)";
	    } else if (m instanceof Package) {
		name = "(Default Package)";
	    } else {
		name = "";
	    }
	}
	return name;
    }

    public static String getNonTrivialFullName(ProgramModelElement m) {
	String name = m.getFullName();
	if (name == null || name.length() == 0) {
	    if (m instanceof ClassType) {
		name = "(Anonymous Type)";
	    } else if (m instanceof Package) {
		name = "(Default Package)";
	    } else {
		name = "";
	    }
	}
	return name;	
    }

    
}
