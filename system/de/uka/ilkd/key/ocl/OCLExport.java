// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//
//


package de.uka.ilkd.key.ocl;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.casetool.UMLModelClass;
import de.uka.ilkd.key.casetool.together.TogetherModelMethod;


/** Export OCL specifications to a file */
public class OCLExport {

    private File file;
    private UMLModelClass cls[];
    private FileWriter out;

    private final static String SEP = "\n";
    
    private boolean adHocWarningAboutQualifications;

    public OCLExport(UMLModelClass cls, FileWriter out){
        this.cls = new UMLModelClass[1];
        this.cls[0] = cls;
        this.out = out;
        adHocWarningAboutQualifications = false;
    }

    public OCLExport(UMLModelClass[] cls, FileWriter out){
        this.cls = cls;
        this.out = out;
        adHocWarningAboutQualifications = false;
    }

    /** get OCL specs (invariant, pre-/posts for methods) for one class */
    private String getOCL(UMLModelClass c)
    {
        String result = "";

        String cName = c.getClassName();

        String inv = c.getMyInv();
        if (inv != null && !inv.equals("")) {
            result += "context " + cName + "\ninv: " + inv + "\n";
        }
        
        Vector ops = c.getOps();
        for (int i = 0; i < ops.size(); i++) {
            ModelMethod meth = (ModelMethod) (ops.elementAt(i));

            String pre = meth.getMyPreCond();
            String post = meth.getMyPostCond();

            if (pre != null && ! pre.equals("")) { 
                pre = "pre: " + pre + "\n"; 
            } else {
                pre = "";
            }
            
            if (post != null && ! post.equals("")) {
                post = "post: " + post + "\n";
            } else {
                pre = "";
            }
            
            if (pre != "" || (post != null && !post.equals(""))) {
                // bug:
                // we can only qualify types correctly if we have
                // a TogetherReprModelMethod
                if (meth instanceof TogetherModelMethod) {
                    result += "\ncontext " + cName + "::" +
                        ((TogetherModelMethod) 
                            meth).getCallSignatureQualified() 
                        + "\n";
                } else {
                    adHocWarningAboutQualifications = true;
                    result += "\ncontext " + cName + "::" +
                        meth.getCallSignature() + "\n";
                }
                result += pre + post;
            }
        }
        
        return result;
    }

    public void export() throws IOException
    {
        // type: key=String (package name), value = String (OCL text)
        // used since we need to group specifications by package in output file
        HashMap packages = new HashMap(); 
        
        // collect OCL specs from all classes in array cls:
        for (int i = 0; i < cls.length; i++) {
            String ocl = getOCL(cls[i]);
            if (ocl != null && ! ocl.equals("")) {
                String pack = cls[i].getContainingPackage();
                if (pack == null || pack.equals("")) { 
                    // put everything in a package by default
                    pack = "NOPACKAGE"; 
                } else {
                    // Java package notation differs from OCL
                    pack = pack.replaceAll("\\.","::");
                }

                String oldPackSpec = (String) packages.get(pack);
                if (oldPackSpec == null) {
                    packages.put(pack, ocl);
                } else {
                    packages.put(pack, oldPackSpec + "\n" + ocl);
                }
            }
        }

        // print all OCL specs in the hashmap packages:
        if (adHocWarningAboutQualifications) {
            // add comment to OCL file with warning about qualification
            out.write("--\n-- WARNING: could not qualify parameter and return types  correctly; this file might not be valid OCL.\n--\n");
        }
        Iterator it = packages.keySet().iterator();
        while (it.hasNext()) {
            String pack = (String) it.next();
            String spec = (String) packages.get(pack);
            
            if (spec != null && ! spec.equals("")) {
                out.write("package " + pack + "\n" + spec + "\nendpackage\n\n");
            }
        }
    }
}

