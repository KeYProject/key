# This file is part of KeY - Integrated Deductive Software Design
# Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
#                         Universitaet Koblenz-Landau, Germany
#                         Chalmers University of Technology, Sweden
#
# The KeY system is protected by the GNU General Public License.
# See LICENSE.TXT for details.



BUILD_FILE=build-$(ECLIPSE_VERSION).xml

# Set windowing system to be used, normally gtk.
# Needed since the swt libraries are specific to the underlying
# windowing system
WS=gtk

# enable verbose ant outputs by commenting out the following line
#VERBOSE=-verbose

.PHONY: export

export: 
ifdef ECLIPSE_HOME
	java -cp $(ECLIPSE_HOME)/startup.jar org.eclipse.core.launcher.Main \
	-application org.eclipse.ant.core.antRunner -buildfile $(BUILD_FILE) \
	-Declipse_home=$(ECLIPSE_HOME) -Dws=$(WS) $(VERBOSE) zip.plugin
	rm -rf workspace
else
	@echo
	@echo "!! Environment variable ECLIPSE_HOME not specified !!"
	@echo "Point this to the base of your eclipse installation to build"
	@echo "the plug-in."
endif

clean:
	rm -f ProofVisualization.jar ProofVisualizationsrc.zip ProofVisualization_*.zip
	rm -rf workspace
