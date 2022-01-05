/*
 * @(#)SerialMethodSubWriter.java	1.20 00/02/02
 *
 * Copyright 1998-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import com.sun.javadoc.*;
import com.sun.tools.doclets.*;
import java.util.*;

/**
 * Generate serialized form for Serializable/Externalizable methods.
 * Documentation denoted by the <code>serialData</code> tag is processed.
 *
 * @author Joe Fialli
 */
public class SerialMethodSubWriter extends MethodSubWriter {
    public SerialMethodSubWriter(SubWriterHolderWriter writer, 
                                 ClassDoc classdoc) {
        super(writer, classdoc);
    }

    public List members(ClassDoc cd) {
	return Util.asList(cd.serializationMethods());
    }

    protected void printHeader(ClassDoc cd) {
        writer.anchor("serialized_methods");
        writer.printTableHeadingBackground(writer.getText("doclet.Serialized_Form_methods"));

	// Specify if Class is Serializable or Externalizable.

        writer.p();

	if (cd.isSerializable() && !cd.isExternalizable()) {
            if (members(cd).size() == 0) {
		String msg =
		    writer.getText("doclet.Serializable_no_customization");
		writer.print(msg);
		writer.p();
	    }
	}
    }

    protected void printMember(ClassDoc cd, ProgramElementDoc member) {
        ExecutableMemberDoc emd = (ExecutableMemberDoc)member;
        String name = emd.name();
        printHead(emd);
        printFullComment(emd);
    }

    protected void printSerialDataTag(Tag[] serialData) {
        if (serialData != null && serialData.length > 0) {
            writer.dt();
            writer.boldText("doclet.SerialData");
            writer.dd();
	    for (int i = 0; i < serialData.length; i++)
		writer.printInlineComment(serialData[i]);
        }
    }

    /**
     * Print comments, See tags and serialData for SerialMethods.
     */
    protected void printTags(ProgramElementDoc member) {
        MethodDoc method = (MethodDoc)member;
	Tag[] serialData = method.tags("serialData");
	Tag[] sinces = method.tags("since");
        SeeTag[] sees = method.seeTags();
        if (serialData.length + sees.length + sinces.length > 0) {
            writer.dd();
            writer.dl();
	    printSerialDataTag(serialData);
            writer.printSinceTag(method);
            writer.printSeeTags(method);
            writer.dlEnd();
            writer.ddEnd();
	} else {
	    if (method.name().compareTo("writeExternal") == 0) {
		serialWarning("doclet.MissingSerialDataTag",
			    method.containingClass().qualifiedName(),
			    method.name());
	    }
	}
    }

    /**
     * Print header even if there are no serializable methods.
     */
    public void printMembers() {
        if (members(classdoc).size() > 0) {
	    super.printMembers();
        }
    }

    public void buildVisibleMemberMap() {
      // Do nothing.
    }
}


