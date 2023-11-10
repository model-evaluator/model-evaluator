package model.function;

import org.javers.core.metamodel.annotation.DiffInclude;

import model.url.Url;

public class CreateBlob extends Event {
	
	@DiffInclude
	public String url;
	
	public CreateBlob() {
		
	}

}
