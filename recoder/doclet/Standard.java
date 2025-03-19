/*
 * @(#)Standard.java	1.41 00/02/02
 *
 * Copyright 1997-2000 Sun Microsystems, Inc. All Rights Reserved.
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
 * The class with "start" method, calls individual Writers.
 *
 * @author Atul M Dambalkar
 * @author Robert Field
 */
public class Standard {

    /**
     * The "start" method as required by Javadoc.
     *
     * @param Root
     * @see com.sun.javadoc.Root
     * @return boolean
     */
    public static boolean start(RootDoc root) throws IOException {
        try { 
            configuration().setOptions(root);
            (new Standard()).startGeneration(root);
        } catch (DocletAbortException exc) {
	  //exc.printStackTrace();
            return false; // message has already been displayed
        }
        return true;
    }
        
    /**
     * Return the configuration instance. Create if it doesn't exist.
     * Override this method to use a different
     * configuration.
     */
    public static ConfigurationStandard configuration() {
        if (HtmlDocWriter.configuration == null) {
            HtmlDocWriter.configuration = new ConfigurationStandard();
        }
        return (ConfigurationStandard)HtmlDocWriter.configuration;
    }

    /**
     * Start the generation of files. Call generate methods in the individual
     * writers, which will in turn genrate the documentation files. Call the
     * TreeWriter generation first to ensure the Class Hierarchy is built
     * first and then can be used in the later generation.
     *
     * For new format.
     *
     * @see com.sun.javadoc.RootDoc
     */
    protected void startGeneration(RootDoc root) throws DocletAbortException {
        if (root.classes().length == 0) {
            configuration().standardmessage.
                        error("doclet.No_Public_Classes_To_Document");
            return;
        }

        if (configuration().topFile.length() == 0) {
            configuration().standardmessage.
                        error("doclet.No_Non_Deprecated_Classes_To_Document");
            return;
        }            

        boolean nodeprecated = configuration().nodeprecated;

        String configdestdir = configuration().destdirname;
        String confighelpfile = configuration().helpfile;
        String configstylefile = configuration().stylesheetfile;

        performCopy(configdestdir, confighelpfile);
        performCopy(configdestdir, configstylefile);

        ClassTree classtree = new ClassTree(root, nodeprecated);

        // do early to reduce memory footprint
        if (configuration().classuse) {
            ClassUseMapper.generate(root, classtree);
        }

        IndexBuilder indexbuilder = new IndexBuilder(root, nodeprecated);
        PackageDoc[] packages = configuration().packages;

        if (configuration().createtree) {
            TreeWriter.generate(classtree);
        }

        if (configuration().createindex) {
            if (configuration().splitindex) {
                SplitIndexWriter.generate(indexbuilder);
            } else {
                SingleIndexWriter.generate(indexbuilder);
            }
        }

        if (!(configuration().nodeprecatedlist || nodeprecated)) { 
            DeprecatedListWriter.generate(root);
        }

        AllClassesFrameWriter.generate(new IndexBuilder(root, nodeprecated, 
                                                        true));

        FrameOutputWriter.generate();

        PackagesFileWriter.generate();
            
        if (configuration().createoverview) {
            PackageIndexWriter.generate(root);
        }
        
        if (packages.length > 1) {
            PackageIndexFrameWriter.generate();
        }

        for(int i = 0; i < packages.length; i++) {
            PackageDoc prev = (i == 0)? 
                              null:
                              packages[i-1];
            PackageDoc packagedoc = packages[i];
            PackageDoc next = (i+1 == packages.length)? 
                              null:
                              packages[i+1];
            PackageWriter.generate(packages[i], prev, next);
            if (configuration().createtree) {
                PackageTreeWriter.generate(packages[i], prev, next, 
                                           nodeprecated);
            }
            PackageFrameWriter.generate(packages[i]);
        }

        generateClassFiles(root, classtree);

        SerializedFormWriter.generate(root);

        PackageListWriter.generate(root);

        if (configuration().helpfile.length() == 0 &&
               !configuration().nohelp) {
            HelpWriter.generate();
        }
        if (configuration().stylesheetfile.length() == 0) {
            StylesheetWriter.generate();
        }
    }

    protected void generateClassFiles(RootDoc root, ClassTree classtree) 
                               throws DocletAbortException {
        ClassDoc[] classes = root.specifiedClasses();
        List incl = new ArrayList();
        for (int i = 0; i < classes.length; i++) {
            ClassDoc cd = classes[i];
            if (cd.isIncluded() && isGeneratedDoc(cd)) {
                incl.add(cd);
            }
        }
        ClassDoc[] inclClasses = new ClassDoc[incl.size()];
        for (int i = 0; i < inclClasses.length; i++) {
            inclClasses[i] = (ClassDoc)incl.get(i);
        }
        generateClassCycle(inclClasses, classtree, true);
        PackageDoc[] packages = configuration().packages;
        for (int i = 0; i < packages.length; i++) {
            PackageDoc pkg = packages[i];
            generateClassCycle(pkg.interfaces(), classtree, false);
            generateClassCycle(pkg.ordinaryClasses(), classtree, false);
            generateClassCycle(pkg.exceptions(), classtree, false);
            generateClassCycle(pkg.errors(), classtree, false);
        }
    }

    protected String classFileName(ClassDoc cd) {
        return cd.qualifiedName() + ".html";
    }

    /**
     * Instantiate ClassWriter for each Class within the ClassDoc[]
     * passed to it and generate Documentation for that.
     */
    protected void generateClassCycle(ClassDoc[] arr, ClassTree classtree,
                            boolean nopackage) throws DocletAbortException {
        Arrays.sort(arr);
        for(int i = 0; i < arr.length; i++) {
            if (configuration().nodeprecated && 
                     arr[i].tags("deprecated").length > 0) {
                continue;
            }
            ClassDoc prev = (i == 0)? 
                            null:
                            arr[i-1];
            ClassDoc curr = arr[i];
            ClassDoc next = (i+1 == arr.length)? 
                            null:
                            arr[i+1];

	    String sourcepath = configuration().sourcepath;  //new       
	    if (sourcepath == null && configuration().linksources) {
		System.out.println("No sourcepath information from which to construct links to source files."); //new
		configuration().linksources = false;
            } //new
            ClassWriter.generate(curr, prev, next, classtree, nopackage);
        }
    }

    /**
     * Check for doclet added options here. 
     *
     * @return number of arguments to option. Zero return means
     * option not known.  Negative value means error occurred.
     */
    public static int optionLength(String option) {
        return configuration().optionLength(option);
    }

    /**
     * Check that options have the correct arguments here. 
     * <P>
     * This method is not required and will default gracefully
     * (to true) if absent.
     * <P>
     * Printing option related error messages (using the provided
     * DocErrorReporter) is the responsibility of this method.
     *
     * @return true if the options are valid.
     */
    public static boolean validOptions(String options[][], 
                                       DocErrorReporter reporter) 
                                throws IOException {
        return configuration().validOptions(options, reporter);
    }

    protected void performCopy(String configdestdir, String filename) 
                        throws DocletAbortException {
        try {
            String destdir = (configdestdir.length() > 0)? 
                             destdir = configdestdir + File.separatorChar: ""; 
            if (filename.length() > 0) {
                File helpstylefile = new File(filename);
                String parent = helpstylefile.getParent();
                String helpstylefilename = (parent == null)? 
                           filename:
                           filename.substring(parent.length() + 1);
                File desthelpfile = new File(destdir + helpstylefilename); 
                if (!desthelpfile.getCanonicalPath().equals(
                                  helpstylefile.getCanonicalPath())) {
                    configuration().standardmessage.
                                      notice("doclet.Copying_File_0_To_File_1",
                           helpstylefile.toString(), desthelpfile.toString());
                    Util.copyFile(desthelpfile, helpstylefile);
                }
            }
        } catch (IOException exc) {
            configuration().standardmessage.
               error("doclet.perform_copy_exception_encountered", 
                                                   exc.toString());
            throw new DocletAbortException();
        }
    }

    /**
     * Return true if the doc element is getting documented, depending upon 
     * -nodeprecated option and @deprecated tag used. Return true if 
     * -nodeprecated is not used or @deprecated tag is not used.
     */ 
    public static boolean isGeneratedDoc(Doc doc) {
        if (!configuration().nodeprecated) {
            return true;
        }
        return (doc.tags("deprecated")).length == 0;
    }
        
} 
        

