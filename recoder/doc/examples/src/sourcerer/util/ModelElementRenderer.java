package sourcerer.util;

import java.awt.Component;

import javax.swing.DefaultListCellRenderer;
import javax.swing.JList;

import recoder.ModelElement;
import recoder.convenience.Format;


public class ModelElementRenderer extends DefaultListCellRenderer {

    private final String format;

    public ModelElementRenderer() {
	this(null);
    }

    public ModelElementRenderer(String format) {
	if (format == null) {
	    format = "%c";
	}
	this.format = format;
    }

    public Component getListCellRendererComponent
	(JList list, Object value, int index, 
	 boolean isSelected, boolean hasFocus) {	    
	super.getListCellRendererComponent
	    (list, value, index, isSelected, hasFocus);
	if (value == null) {
	    setText("");
	} else {
	    setText(Format.toString(format, (ModelElement)value));
	}
	return this;
    }
}

