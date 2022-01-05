package sourcerer.util;

import java.awt.Font;

import javax.swing.plaf.FontUIResource;
import javax.swing.plaf.metal.DefaultMetalTheme;

public class ThinMetalTheme extends DefaultMetalTheme {
	    
    private FontUIResource font;
    {
	font = super.getControlTextFont();
	font = new FontUIResource(new Font(font.getName(), Font.PLAIN, font.getSize()));
    }
    
    public FontUIResource getControlTextFont() {
	return font;
    }	    
    public FontUIResource getMenuTextFont() {
	return font;
    }
    public FontUIResource getSystemTextFont() {
	return font;
    }      
    public FontUIResource getUserTextFont() {
	return font;
    }	    
    public FontUIResource getWindowTitleFont() {
	return font;
    }
}
