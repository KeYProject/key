// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

/** 
 * @author Kristofer Johannisson and Hans-Joachim Daniels (daniels@ira.uka.de)
 */

package de.uka.ilkd.key.ocl.gf;

import java.io.*;
import java.util.Collection;
import java.util.Iterator;
import java.util.Vector;
import java.util.logging.Level;
import java.util.logging.Logger;

import javax.swing.ProgressMonitor;

import de.uka.ilkd.key.casetool.UMLOCLModel;
import de.uka.ilkd.key.casetool.together.TogetherModelMethod;

/** 
 * control object interfacing KeY with GF.
 * Saves the editor from knowing, that KeY exists 
 */
public abstract class GFinterface {
        public final static String gfBinaryCmd = "gf";
        public final static String u2gfBinaryCmd = "umltypes2gf";
        public final static String modelModulName = "FromUMLTypes";
        protected final static String modelinfoUmltypesFilename = "modelinfo.umltypes";
        /**
         * get's defined in subclass @see TogetherGFInterface.
         * Contains the place where modelinfo.umltypes is put
         */
        public String modelInfoUmltypes;
        
        private static TempGrammarFiles tgf;
        protected static Logger logger = Logger.getLogger(GFinterface.class.getName());
        
        final static boolean AUTO_GENERATE = true; // automatically generate grammars before starting editor
        /**
         * get's defined in subclass @see TogetherGFInterface.
         */
        protected UMLOCLModel model;
        protected Collection fromObject;
        protected Collection inOCL;
        protected Collection unknownAdded;
        
        /** 
         * path to the Together project, get's written in subclass 
         */
        protected String projectRoot;
        
        
        /**
         * Creates a new temporary directory and copies the grammars
         * in a subdirectory called grammars2 of it.
         * @return the location of the created grammars2 directory
         */
        private String copyGrammars() {
                if (tgf == null) { // only copy if necessary
                        try {
                                tgf = new TempGrammarFiles();
                        }
                        catch (IOException e) {
                                System.err.println("Could not copy GF OCL grammars.");
                                System.err.println("e.getLocalizedMessage(): " + e.getLocalizedMessage());
                                System.err.println("e.toString(): " + e);
                                System.err.println("stacktrace: ");
                                System.err.println(e.getStackTrace().toString()); 
                                // e.printStackTrace(System.err);
                                //		Debug.out(e);
                                return null;
                        }
                }
                return tgf.path2grammars2();
        }
        
        
        /**
         * Starts the GF editor for OCL for editing a class invariant
         * @param classname The name of the class whose invariant should be edited
         * @param pack the package of the class whose invariant should be edited
         * @param ocl the OCL invariant
         * @param cci a special callback class, must be properly initialized
         * @param pm to monitor the loading progress. May be null
         * @param absFromTogether The abstract syntax tree saved as a JavaDoc 
         * from previous runs
         * @return message to Together (only if something went wrong?)
         */
        public String editClassInvariant(String classname, String pack, String ocl, CallbackClassInv cci, ProgressMonitor pm, String absFromTogether) {
                Utils.tickProgress(pm, 2340, "Construction the class name for GF");
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer("previous invariant is: '" + ocl + "'");
                }
                //Qualifying invC mit 'core.' is sth. the current GF does not like
                String gfClassName = constructClassNameForGF(classname, pack, true) 
                	+ " (\\this -> invCt ?)";
                
                Utils.tickProgress(pm, 2350, "Copying grammars to temporary directory");
                String grammarsDir = copyGrammars();
                Utils.tickProgress(pm, 3430, "Creating model information");
                createModelinfo();
                Utils.tickProgress(pm, 3600, "generating grammars");
                if (!callUmltypes2gf(grammarsDir, false)) {
                        return "an error occurred";
                }
                Utils.tickProgress(pm, 3910, "Constructing abstract syntax tree");
                String abs = constructAbs("inv: " + ocl, grammarsDir, pack, classname);
                if ("".equals(abs)) {
                        //seemingly, either sth. unparsable or nothing
                        //was saved as real OCL. So try if sth. was saved as abstract
                        if (absFromTogether != null) {
                                abs = absFromTogether;
                        }
                }

                Utils.tickProgress(pm, 5150, "Calling the GF editor");
                String[] call2gf = constructCallToGF(grammarsDir);
                cci.setGrammarsDir(grammarsDir);
                GFEditor2.mainConstraint(call2gf, cci, abs, gfClassName, pm);
                return ""; // all is well
        }
        
        /** Start GF editor for editing pre-/postcondition of a method/operation
         * @param classname the name of class of the operation
         * @param pack the name of the package the class is in
         * @param opersig signature of the operation
         * @param pre string containg OCL precondition (currently ignored)
         * @param post string containg OCL postcondition (currently ignored)
         * @param isQuery if the method is a query
         * @param pm to monitor the loading progress. May be null
         * @param absFromTogether The abstract syntax tree saved as a JavaDoc 
         * from previous runs
         * @return message to Together (if something went wrong)
         */
        public String editPrePost(String classname, String pack, String opersig, String pre, String post, CallbackPrePost cpp, boolean isQuery, ProgressMonitor pm, String absFromTogether)
        {
                Utils.tickProgress(pm, 2340, "Construction the operation's name for GF");
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer("previous precondition is : '" + pre + "'");
                        logger.finer("previous postcondition is: '" + post + "'");
                }
                Vector paramNames = new Vector();
                
//              Qualifying invC mit 'core.' is sth. the current GF does not like                
                StringBuffer gfOperTree = new StringBuffer(constructOperNameForGF(classname, pack, opersig, paramNames, isQuery));
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer("GF fun name: " + gfOperTree);
                }
                gfOperTree.append(" (\\this");
 
                for (Iterator it = paramNames.iterator(); it.hasNext(); ) {
                        gfOperTree.append(",").append(it.next().toString());
                }
                gfOperTree.append(" -> prepostCt ? ? )");
                Utils.tickProgress(pm, 2350, "Copying grammars to temporary directory");
                String grammarsDir = copyGrammars();
                
                Utils.tickProgress(pm, 3430, "Creating model information");
                createModelinfo();
                Utils.tickProgress(pm, 3600, "generating grammars");
                if (!callUmltypes2gf(grammarsDir, false)) {
                        return "an error occurred";
                }
                Utils.tickProgress(pm, 3910, "Constructing abstract syntax tree");
                String oclConstraint = "";
                if (pre != null && !("".equals(pre))) {
                        oclConstraint = "pre: " + pre + "\n";
                }
                if (post != null && !("".equals(post))) {
                        oclConstraint = oclConstraint + "post: " + post;
                }
                String abs = constructAbs(oclConstraint, grammarsDir, pack, classname + "::" + opersig);

                if ("".equals(abs)) {
                        //seemingly, either sth. unparsable or nothing
                        //was saved as real OCL. So try if sth. was saved as abstract
                        if (absFromTogether != null) {
                                abs = absFromTogether;
                        }
                }
                if ("".equals(abs)) return "Failed";
                
                Utils.tickProgress(pm, 5150, "Calling the GF editor");
                
                if (logger.isLoggable(Level.FINE)) {
                        logger.fine("abs: '" + abs + "'");
                }
                String[] call2gf = constructCallToGF(grammarsDir);
                
                cpp.setGrammarsDir(grammarsDir);
                GFEditor2.mainConstraint(call2gf, cpp, abs, gfOperTree.toString(), pm);
                
                return ""; // everything should be OK
        }
        
        /**
         * puts the context in front of ocl. Not very fancy 
         * @param ocl the OCL constraint including inv: respectively pre: ... post: 
         * @param context either the class for inv: or the operation
         * including the class for pre: ... post: .
         * The package is not needed, that get's wrapped around the context.
         * @return just the concatenation of context, $context and OCL
         */
        private String setupContext(String ocl, String context) {
                String result = "context " + context + "\n" + ocl;
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer(result);
                }
                return result;
        }
        
        /**
         * calls ocl2nl to produce a GF abstract syntax tree
         * @param ocl the actual OCL constraint including inv: 
         * respectively pre: ... post:
         * @param grammarsDir the temp directory where the GF grammars are stored
         * @param pack the package in which the constraint should hold
         * @param context the context for the constraint, be it the class or
         * class.operation
         * @return a GF AST for the constraint, if parsing succeeds, "", if not
         */
        private String constructAbs(String ocl, String grammarsDir, String pack, String context) {
                String abs;
                if (ocl == null || ocl.trim().equals("inv:") || ocl.trim().equals("pre: \npost:")) {
                        abs = "";
                } else {
	                File oclFile;
	                try {
	                        String toParse = setupContext(ocl, context);
	                        toParse = wrapOCLwithPackage(toParse, pack);
	                        oclFile = TempGrammarFiles.createOCLtmp(toParse);
	                } catch (IOException e) {
	                        System.err.println(e.getLocalizedMessage());
	                        e.printStackTrace();
	                        return e.getLocalizedMessage();
	                }
	                abs = callOcl2Nl(oclFile, grammarsDir, true, false, "");
                }
                return abs;
        }
        
        /**
         * Puts together the call to GF that is to be executed.
         * Expects that 'gf' is in the path
         * @param grammarsDir The directory where the grammars reside
         * @return the command, ready to be executed
         */
        private String[] constructCallToGF(String grammarsDir) {
                String gfOptions = System.getProperty("key.gfoptions");
                //OCL has to come last so that the printnames from OCL get read.
                //If the order is changed, the user would have to change the
                //menu language to OCL to get that effect. TODO
                int len = 5+ ("-src".equals(gfOptions) ? 1: 0);
                String[] s = new String[len];
                int i = 0;
                s[i++] = gfBinaryCmd;
                if ("-src".equals(gfOptions)) s[i++]="-src";
                s[i++]="-java";
                s[i++]=grammarsDir + File.separator + GFinterface.modelModulName + "Ger.gf";
                s[i++]=grammarsDir + File.separator + GFinterface.modelModulName + "Eng.gf";
                s[i++]=grammarsDir + File.separator + GFinterface.modelModulName + "OCL.gf";
                
                return s;
        }
        
        
        /**
         * produces the fun name for a class with package, that can be used in 
         * the context of the FromUMLTypes grammars
         * @param classname the name of the class that is to be given a new name.
         * Is expected without any flavouring, just the class name
         * @param pack the package of the class that is to be given a new name
         * in the usual.java.notation
         * @param constr true iff a trailing _Constr should be appended
         * @return the GF fun name for the class
         */
        private String constructClassNameForGF(final String classname, final String pack, boolean constr) {
                String result = "";
                String newPack = "";
                
                if (pack == null || pack.equals("")) {
                        newPack = "NOPACKAGE";
                } else {
                        newPack = pack.replaceAll("[\\.]", "P_");
                }
                
                result = newPack + "P_" + classname + "C";
                if (constr) {
                        result += "_Constr";
                }
                //currently GF does not accept module qualified fun names
                //result = GFinterface.modelModulName + "." + result;
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer("constructedGFClassName: " + result);
                }
                return result;
        }

        /**
         * produces the GF fun name for a class in the double colon notation.
         * It maps the OCL predefined types to their GF name, which means,
         * that one cannot have them without packages, since those OCL types
         * and the userdefined same name types clash.
         * @param colonNotation a class name with packages like in
         * <pre>java::math::BigInteger</pre>
         * @return the GF fun notation like <pre>javaP_mathP_BigIntegerC</pre> or <pre>Integer</pre>
         */
        private String constructClassNameForGF(final String colonNotation) {
                //String baseName = colonNotation.replaceAll("Sequence \\((.*)\\)","$1");
                
                String newName = colonNotation.replaceAll("Sequence \\((.*)\\)","Sequence_$1");
                if (newName.indexOf("::") == -1) {
                        if (logger.isLoggable(Level.FINER)) {
                                logger.finer("transformTypeJava2OCL :" + TogetherModelMethod.transformTypeJava2OCL(colonNotation));
                        }
                        if (colonNotation != TogetherModelMethod.transformTypeJava2OCL(colonNotation)) {
                                newName = "NOPACKAGEP_" + newName; 
                        }
                        newName =  newName + "C";
                } else {
                        newName = newName.replaceAll("::","P_");
                        newName += "C";
                }
                return newName.toString();
        }

        /**
         * transform the given method's representation into that of 
         * @param classname The name of class the method belongs to, 
         * without package information 
         * @param pack the package of this class
         * @param opersig the fully qualified signature of the method like in
         * <pre>operation1(ios : java::io::PrintStream, bi : java::math::BigInteger) : java::util::Vector</pre>
         * @param parameterNames This Vector will be filled with the parameter 
         * names of the operation (Strings)
         * @param isQuery TODO
         * @return the fun in GF that belongs to this method, like in
         * <pre>NOPACKAGEP_CardExceptionC_operation1_javaP_ioP_PrintStreamC_javaP_mathP_BigIntegerC_Oper_Constr</pre> 
         */
        private String constructOperNameForGF(final String classname, final String pack, final String opersig, final Vector parameterNames, boolean isQuery) {
                final String clss = constructClassNameForGF(classname, pack, false);
                final StringBuffer newName = new StringBuffer(clss);
                newName.append("_");
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer("opersig: "+ opersig);
                }
                SigTokenizer st = new SigTokenizer(new StringBuffer(opersig));
                newName.append(st.operName).append("_");                
                for (Iterator it = st.paramTypes.iterator(); it.hasNext(); ) {
                        newName.append(constructClassNameForGF((String)it.next())).append("_");
                }
                for (Iterator it = st.paramNames.iterator(); it.hasNext(); ) {
                        parameterNames.add(it.next());
                }

                if (st.retType != null) {
                        parameterNames.add(0, "result");
                }
                //String returnType = constructClassNameForGF(st.retType);
                //logger.finer("return type : '" + returnType + "'");
                newName.append("Oper_Constr");
                
                return newName.toString();
        }
        
        
        /**
         * Wraps an OCL statement with a PACKAGE section
         * @param ocl the OCL statement to be wrapped
         * @param pack the package name in Java notation
         * @return the OCL grammar notation, NOPACKAGE if package name is empty
         */
        private String wrapOCLwithPackage(final String ocl, final String pack) {
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer("wrap: pack='" + pack + "'  --  ocl='" + ocl + "'");
                }
                String oclPackage;
                if (pack == null || pack.equals("")) {
                        oclPackage = "NOPACKAGE";
                } else {
                        oclPackage = pack.replaceAll("[::]", "\\.");
                }
                String result = "package " + oclPackage + "\n" + ocl + "\nendpackage\n";
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer("wrapped = '" + result + "'");
                }
                return result;
        }
        
        /**
         * calls the external binary ocl2nl, which is expected to be in the
         * path and returns the abstract Syntax tree
         * @param oclFile the file where the ocl constraints are stored. 
         * These get parsed.
         * @param grammarsDir the path of the directory that contains the 
         * OCL-GF2 grammars
         * @param generateTree should ocl2nl produce a GF tree instead of NL text?
         * @param optimize should ocl2nl optimize the output
         * @param format should be one of {"", "html", "latex"}
         * @return the abstract syntax tree for GF of the OCL constraints
         * in oclFile
         */
        private String callOcl2Nl(File oclFile, String grammarsDir,
                                  boolean generateTree, boolean optimize,
                                  String format) {

                int len = 5+ (generateTree ? 1 : 0)+
                    (optimize ? 1 : 0)+
                    (format.equals("") ? 0 : 1);
                String[] call = new String[len];
                int i = 0;
                call[i++]="ocl2nl";
                if (generateTree) call[i++]="-t";
                if (optimize) call[i++]="-o";
                if (format.equals("html"))  call[i++]="-f html";
                if (format.equals("latex")) call[i++]="-f latex";
                call[i++]="-p";
                call[i++]=grammarsDir;
                call[i++]=modelInfoUmltypes;
                call[i++]=oclFile.getAbsolutePath();
                
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer("call to ocl2nl: '" + call +"'");
                }
                
                String s = "";
                StringBuffer result = new StringBuffer("");
                
                try {
                        Process p = Runtime.getRuntime().exec(call);
                        
                        BufferedReader stdInput = new BufferedReader(new 
                                        InputStreamReader(p.getInputStream()));
                        
                        BufferedReader stdError = new BufferedReader(new 
                                        InputStreamReader(p.getErrorStream()));
                        
                        //final String oneConstraint = "[document] ([oneConstraint]"; //old format 
                        final String oneConstraint = "%document% (%oneConstraint%";
                        // read the output from the command
                        while ((s = stdInput.readLine()) != null) {
                                if (logger.isLoggable(Level.FINER)) {
                                        logger.finer(s);
                                }
                                
                                if (generateTree) {
                                    //looks out for %oneConstraint% since the 
                                    //normal GF output can't be switched of at the
                                    //moment
                                    int index = s.indexOf(oneConstraint);
                                    if (index > -1) {
                                            //delete oneConstraint and the corresponding closing bracket
                                            result.append(s.substring(index + oneConstraint.length() + 1, s.length() - 1));
                                    }
                                } else {
                                    result.append(s);
                                }
                        }
                        
                        // read any errors from the attempted command
                        
                        while ((s = stdError.readLine()) != null) {
                                if (!s.trim().equals("")) {
                                        System.err.println("Standard error from "+java.util.Arrays.asList(call));
                                        System.err.println(s);
                                        return "";
                                }
                        }
                }
                catch (IOException e) {
                        System.err.println("error calling ocl2nl:" + e.getMessage());
                        return "";
                }
                
                return result.toString();
        }
        
        /** 
         * create the necessary GF grammars from the information in the UML model of
         * the current project 
         */
        private void createModelinfo() {
                if (AUTO_GENERATE) {
                        ModelExporter me = new ModelExporter(model.getUMLOCLClassifiers());
                        me.export(modelInfoUmltypes);
                }
        }
        
        /**
         * Takes the modelinfo.umltypes file and generates the GF grammars
         * based on what's inside this file
         * @param pathToGrammars The directory where the grammars should be stored
         * @param inclJava all referenced Java should be represented in the grammars
         * @return true, if everything worked fine, otherwise false
         */
        private boolean callUmltypes2gf(String pathToGrammars, boolean inclJava) {
                String[] call = new String[] {
                    u2gfBinaryCmd, "-i",  pathToGrammars, 
                    "-o", pathToGrammars, 
                    (inclJava ? "" : "-j"), modelInfoUmltypes };
                if (logger.isLoggable(Level.FINER)) {
                        logger.finer("call to umltypes2gf: '" + call +"'");
                }
                
                String s = null;
                
                try {
                        Process p = Runtime.getRuntime().exec(call);
                        
                        BufferedReader stdInput = new BufferedReader(new 
                             InputStreamReader(p.getInputStream()));
                        
                        BufferedReader stdError = new BufferedReader(new 
                                        InputStreamReader(p.getErrorStream()));
                        
                        // read the output from the command
                        
                        String out = "";
                        while ((s = stdInput.readLine()) != null) out = out + s;
                        if (!"".equals(out.trim())) {
                            System.err.println("Here is the standard out of the command "+
                                java.util.Arrays.asList(call)+":\n");
                            System.err.println(out);
                        }
                        
                        
                        // read any errors from the attempted command
                        
                        String err = "";
                        while ((s = stdError.readLine()) != null) err = err + s;
                        if (!"".equals(err.trim())) {
                            System.err.println("Here is the standard error of the command "+
                                java.util.Arrays.asList(call)+":\n");
                            System.err.println(err);
                            return false;
                        }
                        
                }
                catch (IOException e) {
                        System.err.println("error calling umltypes2gf:" + e.getMessage());
                        return false;
                }
                return true;
        }	
        
    /** 
     * translate all OCL specs in a text file to NL
     * @param format should be either "html" or "latex"
     */
    public void ocl2nlExport(File oclFile, File nlFile, String format)
    {
        // generate UML model file
        createModelinfo();
        
        // generate grammars
        String grammarsDir = copyGrammars();
        if (! callUmltypes2gf(grammarsDir, false)) {
            System.err.println("ocl2nlExport: grammar generation failed.");
            return;
        } else {
            // call binary ocl2nl, default to HTML
            if (! (format.equals("html") || format.equals("latex"))) {
                format = "html";
            }
            String nl = callOcl2Nl(oclFile, grammarsDir, false, false, format);
            // put NL in a file
            try {
                PrintWriter out = new PrintWriter(
                    new BufferedWriter(new FileWriter(nlFile))); 
                out.print(nl); 
                out.close(); 
            } catch (IOException e) {
                System.err.println("could not write NL translation of OCL file: " + e.getMessage());
            }
        }
    }

}

/**
 * A class that takes an operation's signature and makes the constituents
 * like name, parameters and their types available in this data structure
 * @author hdaniels
 */
class SigTokenizer {
        private final StringBuffer workingsig;
        /**
         * the names of the parameters as Strings
         */
        public Vector paramNames = new Vector();
        /**
         * the types of the parameters in OCL notation as Strings
         */
        public Vector paramTypes = new Vector();
        /**
         * the return type of the operation, null iff void
         */
        public String retType = null;
        /**
         * the name of the given operation
         */
        public final String operName;
        /**
         * lexes the given signature and fills the other fields with 
         * their values
         * @param sig the operation's signature without package
         */
        public SigTokenizer(StringBuffer sig) {
	    this.workingsig = new StringBuffer(sig.toString());
                int index = workingsig.indexOf("(");
                operName = workingsig.substring(0,index);
                workingsig.delete(0,index);
                while (produceNext()) {
                }
        }
        /**
         * cuts through the signature and writes the names and types of the 
         * parameters and the type of the result into the respective fields.
         * Must be called until it returns false
         * @return true iff sth. of the signature is left to parse
         */
        private boolean produceNext() {
                if (workingsig.charAt(0) == '(') {
                        workingsig.deleteCharAt(0);
                        //first parameter
                        return true;
                }
                
                if (workingsig.charAt(0) == ':') {
//                      return type
                        workingsig.delete(0,2);
                        retType = workingsig.toString();
                        return false;
                }
                
                int pindex = workingsig.indexOf(", ");
                if (pindex == -1) {
                        //param) : retType //which exists
                        pindex = workingsig.indexOf(") ");
                }
                if (pindex > 0) {
                        //more parameters exist
                        String s = workingsig.substring(0,pindex);
                        nameType(s);
                        workingsig.delete(0, pindex + 2);
                        return true;
                }
                if (pindex == 0) {
                        //no more params, but return type
                        workingsig.delete(0, pindex + 2);
                        return true;
                }
                //no returntype exists, but last param is Sequence (...)
                pindex = workingsig.indexOf("))");
                if (pindex > -1) {
                        //more parameters exist
                        String s = workingsig.substring(0,pindex + 1);
                        nameType(s);
                        workingsig.delete(0, pindex + 2);
                        return false;
                }
                //no returntype exists, but last param is no Sequence
                pindex = workingsig.indexOf(")");
                if ((pindex > 0) && (pindex == workingsig.length() - 1)) {
                        String s = workingsig.substring(0,pindex);
                        nameType(s);
                        workingsig.delete(0, pindex + 1);
                        return false;
                }
                //what remains is a single ')'
                return false;
        }

        /**
         * takes a pair of parameter name : type and writes both parts
         * into the two Vector fields
         * @param myworkingsig the parameter in the form 
         * <pre>parameterName : parameter::type</pre>
         */
        private void nameType(String myworkingsig){
	                int pindex = myworkingsig.indexOf(" : ");
	                String paramName = myworkingsig.substring(0, pindex);
	                paramNames.add(paramName);
	                myworkingsig = myworkingsig.substring(pindex + 3);//delete ' : ' also
	                String paramTypeCN = myworkingsig;
	                paramTypes.add(paramTypeCN);
        }
}
