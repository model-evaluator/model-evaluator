package model.function;

import org.javers.core.metamodel.annotation.DiffInclude;

import model.BrowsingContext;
import model.Document;
import model.url.Url;

public class CreateIframe extends Event {
	
	@DiffInclude
	public String url;
	
	@DiffInclude
	public String response;
	
	@DiffInclude
	public String newBc;
	
	public CreateIframe() {
		
	}

}
