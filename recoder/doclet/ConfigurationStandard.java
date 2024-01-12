/*
 * @(#)ConfigurationStandard.java	1.20 00/02/02
 *
 * Copyright 1998-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import com.sun.tools.doclets.*;
import com.sun.javadoc.*;
import java.util.*;
import java.io.*;

/**
 * Configure the output based on the command line options. 
 * <p> 
 * Also determine the length of the command line option. For example,
 * for a option "-header" there will be a string argument associated, then the
 * the length of option "-header" is two. But for option "-nohelp" no argument 
 * is needed so it's length is 1. 
 * </p>
 * <p>
 * Also do the error checking on the options used. For example it is illegal to
 * use "-helpfile" option when already "-nohelp" option is used.
 * </p> 
 *
 * @author Robert Field.
 * @author Atul Dambalkar.
 */
public class ConfigurationStandard extends Configuration {

    /**
     * Argument for command line option "-header".
     */
    public String header = "";

    /**
     * Argument for command line option "-footer".
     */
    public String footer = "";

    /**
     * Argument for command line option "-doctitle".
     */
    public String doctitle = "";

    /**
     * Argument for command line option "-windowtitle".
     */
    public String windowtitle = "";

    /**
     * Argument for command line option "-bottom". 
     */
    public String bottom = "";

    /**
     * Argument for command line option "-helpfile".
     */
    public String helpfile = "";

    /**
     * Argument for command line option "-stylesheetfile".
     */
    public String stylesheetfile = "";

    /**
     * True if command line option "-nohelp" is used. Default value is false. 
     */
    public boolean nohelp = false;

    /**
     * True if command line option "-splitindex" is used. Default value is
     * false. 
     */
    public boolean splitindex = false;

    /**
     * False if command line option "-noindex" is used. Default value is true.
     */
    public boolean createindex = true;

    /**
     * True if command line option "-use" is used. Default value is false.
     */
    public boolean classuse = false;

    /**
     * False if command line option "-notree" is used. Default value is true.
     */
    public boolean createtree = true;

    /**
     * True if command line option "-nodeprecated" is used. Default value is
     * false.
     */
    public boolean nodeprecatedlist = false;

    /**
     * True if command line option "-nosince" is used. Default value is
     * false.
     */
    public boolean nosince = false;

    /**
     * True if command line option "-nonavbar" is used. Default value is false.
     */
    public boolean nonavbar = false;

    /**
     * True if command line option "-nooverview" is used. Default value is
     * false 
     */
    private boolean nooverview = false;

    /**
     * True if command line option "-overview" is used. Default value is false.
     */
    public boolean overview = false;

    /**
     * This is true if option "-overview" is used or option "-overview" is not
     * used and number of packages is more than one.
     */
    public boolean createoverview = false;

    /**
     * This is true if option "-serialwarn" is used. Defualt value is false to
     * supress excessive warnings about serial tag. 
     */
    public boolean serialwarn = false;

    /**
     * This is true if option "-linksources" is used. Default value is false to
     * include source code links.
     */
    public boolean linksources = false; //new

    /**
     * The META charset tag used for cross-platform viewing.  
     */
    public String charset = "";

    /**
     * Unique Resource Handler for this package. 
     */
    public static MessageRetriever standardmessage = null;

    /**
     * First file to appear in the right-hand frame in the generated 
     * documentation.
     */
    public String topFile = "";

    /**
     * Constructor. Initialises resource for the
     * {@link com.sun.tools.doclets.MessageRetriever}.
     */
    public ConfigurationStandard() {
        if (standardmessage == null) {
            standardmessage = new MessageRetriever(ResourceBundle.getBundle("resources.standard")); //new - enforce local search for resource bundle
        }
    }

    /**
     * Depending upon the command line options provided by the user, set 
     * configure the output generation environment.
     *
     * @param root Used to retrieve used comand line options.
     */
    public void setSpecificDocletOptions(RootDoc root) {
        String[][] options = root.options();
        for (int oi = 0; oi < options.length; ++oi) {
            String[] os = options[oi];
            String opt = os[0].toLowerCase();
            if (opt.equals("-footer")) {
                footer =  os[1];
            } else  if (opt.equals("-header")) {
                header =  os[1];
            } else  if (opt.equals("-doctitle")) {
                doctitle =  os[1];
            } else  if (opt.equals("-windowtitle")) {
                windowtitle =  os[1];
            } else  if (opt.equals("-bottom")) {
                bottom =  os[1];
            } else  if (opt.equals("-helpfile")) {
                helpfile =  os[1];
            } else  if (opt.equals("-stylesheetfile")) {
                stylesheetfile =  os[1];
            } else  if (opt.equals("-charset")) {
                charset =  os[1];
            } else  if (opt.equals("-nohelp")) {
                nohelp = true;
            } else  if (opt.equals("-splitindex")) {
                splitindex = true;
            } else  if (opt.equals("-noindex")) {
                createindex = false;
            } else  if (opt.equals("-use")) {
                classuse = true;
            } else  if (opt.equals("-notree")) {
                createtree = false;
            } else  if (opt.equals("-nodeprecatedlist")) {
                nodeprecatedlist = true;
            } else  if (opt.equals("-nosince")) {
                nosince = true;
            } else  if (opt.equals("-nonavbar")) {
                nonavbar = true;
	    } else  if (opt.equals("-nooverview")) {
                nooverview = true;
	    } else  if (opt.equals("-overview")) {
                overview = true;
	    } else  if (opt.equals("-serialwarn")) {
                serialwarn = true;
            }  else if (opt.equals("-linksources")) { //new
		linksources = true; //new
	    }
        }
        setCreateOverview();
        setTopFile(root);
    }

    /**
     * Check for doclet added options here. This works exactly like 
     * {@link com.sun.tools.doclets.Configuration#optionLength(String)}. This 
     * will return the length of the options which are added by "standard" 
     * doclet.
     *
     * @param option Option whose length is requested.
     * @return number of arguments to option. Zero return means
     * option not known.  Negative value means error occurred. 
     */
    public int specificDocletOptionLength(String option) {
        if (option.equals("-nodeprecatedlist") ||
            option.equals("-noindex") ||
            option.equals("-notree") ||
            option.equals("-nohelp") ||
            option.equals("-nosince") ||
            option.equals("-splitindex") ||
            option.equals("-use") ||
            option.equals("-nonavbar") ||
            option.equals("-serialwarn") ||
            option.equals("-linksources") || //new
            option.equals("-nooverview")) {
            return 1;
        } else if (option.equals("-help") ) {
            standardmessage.notice("doclet.usage");
            return 1;
        } else if (option.equals("-x") ) {
            standardmessage.notice("doclet.xusage");
            return -1; // so run will end
        } else if (option.equals("-footer") ||
                   option.equals("-header") ||
                   option.equals("-doctitle") ||
                   option.equals("-windowtitle") ||
                   option.equals("-bottom") ||
                   option.equals("-helpfile") ||
                   option.equals("-stylesheetfile") ||
                   option.equals("-link") ||
                   option.equals("-charset") ||
                   option.equals("-overview")) {
            return 2;
        } else if (option.equals("-group") ||
                   option.equals("-linkoffline")) {
            return 3;
        } else {
            return 0;
        }
    }

    /**
     * This checks for the validity of the options used by the user. This works 
     * exactly like
     * {@link com.sun.tools.doclets.Configuration#validOptions(String[][],
     * DocErrorReporter)}. This will validate the options added by the 
     * "standard" doclet. For example, this method will flag an error using
     * the DocErrorReporter if user has used "-nohelp" and "-helpfile" option
     * together.
     * 
     * @param options  Options used on the command line.
     * @param reporter Error reporter to be used.
     * @return true if all the options are valid.
     */
    public boolean specificDocletValidOptions(String options[][],
                                              DocErrorReporter reporter) {
        boolean helpfile = false;
        boolean nohelp = false;
        boolean overview = false;
        boolean nooverview = false;
        boolean splitindex = false;
        boolean noindex = false;
        for (int oi = 0; oi < options.length; ++oi) {
            String[] os = options[oi];
            String opt = os[0].toLowerCase();
            if (opt.equals("-helpfile")) {
                if (nohelp == true) {
                    reporter.printError(standardmessage.getText(
                         "doclet.Option_conflict", "-helpfile", "-nohelp")); 
                    return false;
                }
                if (helpfile == true) {
                    reporter.printError(standardmessage.getText(
                                         "doclet.Option_reuse", "-helpfile")); 
                    return false;
                }
                File help = new File(os[1]);
                if (!help.exists()) {
                    reporter.printError(standardmessage.getText(
				             "doclet.File_not_found", os[1])); 
                    return false;
                }                    
                helpfile = true;
            } else  if (opt.equals("-nohelp")) {
                if (helpfile == true) {
                    reporter.printError(standardmessage.getText(
                         "doclet.Option_conflict", "-nohelp", "-helpfile")); 
                    return false;
                }
                nohelp = true;
            } else if (opt.equals("-overview")) {
                if (nooverview == true) {
                    reporter.printError(standardmessage.getText(
                        "doclet.Option_conflict", "-overview", "-nooverview")); 
                    return false;
                }
                if (overview == true) {
                    reporter.printError(standardmessage.getText(
                                         "doclet.Option_reuse", "-overview")); 
                    return false;
                }
                overview = true;
            } else  if (opt.equals("-nooverview")) {
                if (overview == true) {
                    reporter.printError(standardmessage.getText(
                        "doclet.Option_conflict", "-nooverview", "-overview")); 
                    return false;
                }
                nooverview = true; 
            } else if (opt.equals("-splitindex")) {
                if (noindex == true) {
                    reporter.printError(standardmessage.getText(
                         "doclet.Option_conflict", "-splitindex", "-noindex")); 
                    return false;
                }
                splitindex = true;
            } else if (opt.equals("-noindex")) {
                if (splitindex == true) {
                    reporter.printError(standardmessage.getText(
                         "doclet.Option_conflict", "-noindex", "-splitindex")); 
                    return false;
                }
                noindex = true;
            } else if (opt.equals("-group")) {
                if (!Group.checkPackageGroups(os[1], os[2], reporter)) {
                    return false;
                }
            } else if (opt.equals("-link")) {
                String url = os[1];
                if (!Extern.url(url, url, reporter)) {
                    return false;
                }
            } else if (opt.equals("-linkoffline")) {
                String url = os[1];
                String pkglisturl = os[2];
                if (!Extern.url(url, pkglisturl, reporter)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Decide the page which will appear first in the right-hand frame. It will
     * be "overview-summary.html" if "-overview" option is used or no
     * "-overview" but the number of packages is more than one. It will be 
     * "package-summary.html" of the respective package if there is only one
     * package to document. It will be a class page(first in the sorted order), 
     * if only classes are provided on the command line.
     *
     * @param root Root of the program structure.
     */
    protected void setTopFile(RootDoc root) {
        if (!checkForDeprecation(root)) {
            return;
        } 
        if (createoverview) {
            topFile = "overview-summary.html";
        } else {
            if (packages.length == 0) {
                if (root.classes().length > 0) {
                    ClassDoc[] classarr = root.classes();
                    Arrays.sort(classarr);
                    ClassDoc cd = getValidClass(classarr);
                    topFile = DirectoryManager.getPathToClass(cd);
		}                    
            } else {
                topFile = DirectoryManager.getPathToPackage(packages[0], 
                                                      "package-summary.html");
            }
        } 
    }  
    
    protected ClassDoc getValidClass(ClassDoc[] classarr) {
        if (!nodeprecated) {
            return classarr[0];
        }
        for (int i = 0; i < classarr.length; i++) {
   	    if (classarr[i].tags("deprecated").length == 0) {
                return classarr[i];
            }
        }
        return null;
    }
 
    protected boolean checkForDeprecation(RootDoc root) {
        ClassDoc[] classarr = root.classes();
        for (int i = 0; i < classarr.length; i++) {
	    if (Standard.isGeneratedDoc(classarr[i])) {
                return true;
            }
	 }
         return false;
     }

    /**
     * Generate "overview.html" page if option "-overview" is used or number of
     * packages is more than one. Sets {@link createoverview} field to true.
     */
    protected void setCreateOverview() { 
        if ((overview || packages.length > 1) && !nooverview) {
            createoverview = true;
        }
    }
}
        

