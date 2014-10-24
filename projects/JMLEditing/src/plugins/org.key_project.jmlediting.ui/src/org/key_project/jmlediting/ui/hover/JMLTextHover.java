package org.key_project.jmlediting.ui.hover;

import org.eclipse.jdt.ui.text.java.hover.IJavaEditorTextHover;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.ui.IEditorPart;

/**
 * An {@link IJavaEditorTextHover} to support JML.
 * @author Martin Hentschel
 */
public class JMLTextHover implements IJavaEditorTextHover {
   /**
    * {@inheritDoc}
    */
	@Override
	public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
		return "List of modifiable locations";
	}

   /**
    * {@inheritDoc}
    */
	@Override
	public IRegion getHoverRegion(ITextViewer textViewer, int offset) {
		return null;
	}

   /**
    * {@inheritDoc}
    */
	@Override
	public void setEditor(IEditorPart editor) {
	}
}
