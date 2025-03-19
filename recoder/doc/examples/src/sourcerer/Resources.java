package sourcerer;

import java.awt.Color;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;

import javax.swing.Icon;
import javax.swing.ImageIcon;

public interface Resources {

    class Loader {

	public final static String PATH = "sourcerer/resources/";

	static URL getLocation(String name) {
	    URL url = ClassLoader.getSystemResource(PATH + name);
	    if (url == null) {
		System.err.println("Warning - could not open \"" + name + "\"");
	    }
	    return url;
	}

	static Icon loadIcon(String name) {
	    URL url = getLocation(name);
	    return (url == null) ? null : new ImageIcon(url);
	}

	static String loadText(String name) {
	    URL url = getLocation(name);
	    if (url == null) {
		return null;
	    }

	    StringBuffer sbuf = new StringBuffer(1024);
	    char[] cbuf = new char[1024];
	    try {
		InputStreamReader isr = 
		    new InputStreamReader(url.openStream());
		while (true) {
		    int len = isr.read(cbuf, 0, 1024);
		    if (len < 0) {
			break;
		    }
		    sbuf.append(cbuf, 0, len);
		}
		isr.close();
	    } catch (IOException ioe) {
		System.err.println("Warning - could not open \"" + name + "\"");	    
		return null;
	    }
	    return sbuf.toString();
	}
    }


    /* * * * * * * * * TEXTS * * * * * * * * */

    String BEAN_SHELL_SCRIPT = Loader.loadText("recodershell.bsh");

    URL HELP_PAGE_URL = Loader.getLocation("help.html");

    String WAIT_ANALYZING_TEXT = "Analyzing - please wait...";


    /* * * * * * * * * ICONS * * * * * * * * */

    Icon LOGO_ICON = Loader.loadIcon("Logo.jpg");
    Icon GOTO_ICON = Loader.loadIcon("Zoom16.gif");
    Icon SHOW_ICON = Loader.loadIcon("History16.gif");
    Icon BACK_ICON = Loader.loadIcon("Back16.gif");
    Icon FORWARD_ICON = Loader.loadIcon("Forward16.gif");
    Icon UP_ICON = Loader.loadIcon("Up16.gif");
    Icon SAVEAS_ICON = Loader.loadIcon("SaveAs16.gif");
    Icon EXECUTE_ICON = Loader.loadIcon("Gear16.gif");
    Icon UPDATE_ICON = Loader.loadIcon("Refresh16.gif");


    Icon ABSTRACT_PACKAGE_CLASS_ICON = Loader.loadIcon("AbstractPackageClass12.gif");
    Icon ABSTRACT_PACKAGE_METHOD_ICON = Loader.loadIcon("AbstractPackageMethod12.gif");
    Icon ABSTRACT_PACKAGE_STATIC_CLASS_ICON = Loader.loadIcon("AbstractPackageStaticClass12.gif");
    Icon ABSTRACT_PRIVATE_STATIC_CLASS_ICON = Loader.loadIcon("AbstractPrivateStaticClass12.gif");
    Icon ABSTRACT_PROTECTED_METHOD_ICON = Loader.loadIcon("AbstractProtectedMethod12.gif");
    Icon ABSTRACT_PROTECTED_STATIC_CLASS_ICON = Loader.loadIcon("AbstractProtectedStaticClass12.gif");
    Icon ABSTRACT_PUBLIC_CLASS_ICON = Loader.loadIcon("AbstractPublicClass12.gif");
    Icon ABSTRACT_PUBLIC_METHOD_ICON = Loader.loadIcon("AbstractPublicMethod12.gif");
    Icon ABSTRACT_PUBLIC_STATIC_CLASS_ICON = Loader.loadIcon("AbstractPublicStaticClass12.gif");
    Icon PACKAGE_ICON = Loader.loadIcon("Package12.gif");
    Icon PACKAGE_CLASS_ICON = Loader.loadIcon("PackageClass12.gif");
    Icon PACKAGE_CONSTRUCTOR_ICON = Loader.loadIcon("PackageConstructor12.gif");
    Icon PACKAGE_FIELD_ICON = Loader.loadIcon("PackageField12.gif");
    Icon PACKAGE_FINAL_CLASS_ICON = Loader.loadIcon("PackageFinalClass12.gif");
    Icon PACKAGE_FINAL_FIELD_ICON = Loader.loadIcon("PackageFinalField12.gif");
    Icon PACKAGE_FINAL_METHOD_ICON = Loader.loadIcon("PackageFinalMethod12.gif");
    Icon PACKAGE_FINAL_STATIC_CLASS_ICON = Loader.loadIcon("PackageFinalStaticClass12.gif");
    Icon PACKAGE_FINAL_STATIC_FIELD_ICON = Loader.loadIcon("PackageFinalStaticField12.gif");
    Icon PACKAGE_FINAL_STATIC_METHOD_ICON = Loader.loadIcon("PackageFinalStaticMethod12.gif");
    Icon PACKAGE_METHOD_ICON = Loader.loadIcon("PackageMethod12.gif");
    Icon PACKAGE_STATIC_CLASS_ICON = Loader.loadIcon("PackageStaticClass12.gif");
    Icon PACKAGE_STATIC_FIELD_ICON = Loader.loadIcon("PackageStaticField12.gif");
    Icon PACKAGE_STATIC_METHOD_ICON = Loader.loadIcon("PackageStaticMethod12.gif");
    Icon PRIVATE_CLASS_ICON = Loader.loadIcon("PrivateClass12.gif");
    Icon PRIVATE_CONSTRUCTOR_ICON = Loader.loadIcon("PrivateConstructor12.gif");
    Icon PRIVATE_FIELD_ICON = Loader.loadIcon("PrivateField12.gif");
    Icon PRIVATE_FINAL_CLASS_ICON = Loader.loadIcon("PrivateFinalClass12.gif");
    Icon PRIVATE_FINAL_FIELD_ICON = Loader.loadIcon("PrivateFinalField12.gif");
    Icon PRIVATE_FINAL_METHOD_ICON = Loader.loadIcon("PrivateFinalMethod12.gif");
    Icon PRIVATE_FINAL_STATIC_CLASS_ICON = Loader.loadIcon("PrivateFinalStaticClass12.gif");
    Icon PRIVATE_FINAL_STATIC_FIELD_ICON = Loader.loadIcon("PrivateFinalStaticField12.gif");
    Icon PRIVATE_FINAL_STATIC_METHOD_ICON = Loader.loadIcon("PrivateFinalStaticMethod12.gif");
    Icon PRIVATE_METHOD_ICON = Loader.loadIcon("PrivateMethod12.gif");
    Icon PRIVATE_STATIC_CLASS_ICON = Loader.loadIcon("PrivateStaticClass12.gif");
    Icon PRIVATE_STATIC_FIELD_ICON = Loader.loadIcon("PrivateStaticField12.gif");
    Icon PRIVATE_STATIC_METHOD_ICON = Loader.loadIcon("PrivateStaticMethod12.gif");
    Icon PROTECTED_CLASS_ICON = Loader.loadIcon("ProtectedClass12.gif");
    Icon PROTECTED_CONSTRUCTOR_ICON = Loader.loadIcon("ProtectedConstructor12.gif");
    Icon PROTECTED_FIELD_ICON = Loader.loadIcon("ProtectedField12.gif");
    Icon PROTECTED_FINAL_CLASS_ICON = Loader.loadIcon("ProtectedFinalClass12.gif");
    Icon PROTECTED_FINAL_FIELD_ICON = Loader.loadIcon("ProtectedFinalField12.gif");
    Icon PROTECTED_FINAL_METHOD_ICON = Loader.loadIcon("ProtectedFinalMethod12.gif");
    Icon PROTECTED_FINAL_STATIC_CLASS_ICON = Loader.loadIcon("ProtectedFinalStaticClass12.gif");
    Icon PROTECTED_FINAL_STATIC_FIELD_ICON = Loader.loadIcon("ProtectedFinalStaticField12.gif");
    Icon PROTECTED_FINAL_STATIC_METHOD_ICON = Loader.loadIcon("ProtectedFinalStaticMethod12.gif");
    Icon PROTECTED_METHOD_ICON = Loader.loadIcon("ProtectedMethod12.gif");
    Icon PROTECTED_STATIC_CLASS_ICON = Loader.loadIcon("ProtectedStaticClass12.gif");
    Icon PROTECTED_STATIC_FIELD_ICON = Loader.loadIcon("ProtectedStaticField12.gif");
    Icon PROTECTED_STATIC_METHOD_ICON = Loader.loadIcon("ProtectedStaticMethod12.gif");
    Icon PUBLIC_CLASS_ICON = Loader.loadIcon("PublicClass12.gif");
    Icon PUBLIC_CONSTRUCTOR_ICON = Loader.loadIcon("PublicConstructor12.gif");
    Icon PUBLIC_FIELD_ICON = Loader.loadIcon("PublicField12.gif");
    Icon PUBLIC_FINAL_CLASS_ICON = Loader.loadIcon("PublicFinalClass12.gif");
    Icon PUBLIC_FINAL_FIELD_ICON = Loader.loadIcon("PublicFinalField12.gif");
    Icon PUBLIC_FINAL_METHOD_ICON = Loader.loadIcon("PublicFinalMethod12.gif");
    Icon PUBLIC_FINAL_STATIC_CLASS_ICON = Loader.loadIcon("PublicFinalStaticClass12.gif");
    Icon PUBLIC_FINAL_STATIC_FIELD_ICON = Loader.loadIcon("PublicFinalStaticField12.gif");
    Icon PUBLIC_FINAL_STATIC_METHOD_ICON = Loader.loadIcon("PublicFinalStaticMethod12.gif");
    Icon PUBLIC_METHOD_ICON = Loader.loadIcon("PublicMethod12.gif");
    Icon PUBLIC_STATIC_CLASS_ICON = Loader.loadIcon("PublicStaticClass12.gif");
    Icon PUBLIC_STATIC_FIELD_ICON = Loader.loadIcon("PublicStaticField12.gif");
    Icon PUBLIC_STATIC_METHOD_ICON = Loader.loadIcon("PublicStaticMethod12.gif");

    /* * * * * * * * * COLORS * * * * * * * * */
    
    /**
       Render color for packages.
     */
    Color PACKAGE_COLOR = new Color(96, 96, 0);

    /**
       Render color for types.
     */
    Color TYPE_COLOR = new Color(96, 0, 96);

    /**
       Render color for constructors.
     */
    Color CONSTRUCTOR_COLOR = new Color(0, 96, 96);

    /**
       Render color for methods.
     */
    Color METHOD_COLOR = new Color(0, 96, 0);

    /**
       Render color for variables and fields.
     */
    Color VARIABLE_COLOR = new Color(0, 0, 96);

    /**
       Render color for package references.
     */
    Color PACKAGE_REFERENCE_COLOR = new Color(56, 56, 0);

    /**
       Render color for type references.
     */
    Color TYPE_REFERENCE_COLOR = new Color(56, 0, 56);

    /**
       Render color for constructor references.
     */
    Color CONSTRUCTOR_REFERENCE_COLOR = new Color(0, 56, 56);

    /**
       Render color for method references.
     */
    Color METHOD_REFERENCE_COLOR = new Color(0, 56, 0);

    /**
       Render color for variable and field references.
     */
    Color VARIABLE_REFERENCE_COLOR = new Color(0, 0, 56);

    /**
       Render color for compilation units.
     */
    Color COMPILATION_UNIT_COLOR = new Color(96, 0, 0);


}
