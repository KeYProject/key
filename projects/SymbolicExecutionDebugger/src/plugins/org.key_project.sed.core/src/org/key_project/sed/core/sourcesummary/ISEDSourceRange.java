package org.key_project.sed.core.sourcesummary;

import org.key_project.sed.core.model.ISEDDebugNode;

public interface ISEDSourceRange {
   public int getLineNumber();
   public int getCharStart();
   public int getCharEnd();
   public ISEDDebugNode[] getDebugNodes();
}
