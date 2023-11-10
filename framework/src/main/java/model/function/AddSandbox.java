package model.function;

import org.javers.core.metamodel.annotation.DiffInclude;

import model.BrowsingContext;

public class AddSandbox extends Event {
	
	@DiffInclude
	public String sandBc;
	
	public AddSandbox() {
		
	}

}
