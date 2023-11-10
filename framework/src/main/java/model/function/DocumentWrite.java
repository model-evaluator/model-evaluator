package model.function;

import org.javers.core.metamodel.annotation.DiffInclude;

import model.BrowsingContext;
import model.Document;

public class DocumentWrite extends Event {
	
	@DiffInclude
	public String newEl;
	
	@DiffInclude
	public String targetBc;
	
	public DocumentWrite() {
		
	}

}
