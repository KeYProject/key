DOCLET=-docletpath "../../doclet" -doclet Standard -sourcepath "../.."/$(SRC_DIR)
#DOCLET=-docletpath "../../doclet.jar" -doclet com.c2_tech.doclets.TexDoclet -sourcepath "../.."/$(SRC_DIR)


DOC=-javadoc $(DOCLET) \
	-noindex -notree -nohelp \
	-author \
        -linksources \
        -stylesheetfile ../recoder.css \
        -windowtitle $(BASENAME_C)' Library '$(VERSION) \
        -doctitle $(BASENAME_C)' '$(VERSION)' Library Specification' \
        -header $(BASENAME_C)' '$(VERSION) \
         -J-mx96m -J-Xmx96m 



# -use \
# -overview compost.html
# -splitIndex

#DOC=doc++ -H -A -J -k


build: ZERO
	$(DOC) $(DOC_PACKAGES)

clean:
	@rm -f *.html
	@rm -f $(find -name "*~")
	@rm -fr $(BASENAME)

ZERO:   # special target, leave empty

