package model;

import java.util.ArrayList;
import java.util.List;

import org.javers.core.metamodel.annotation.Id;

import model.url.Url;

public class Document {
	
	@Id
	public String name;
	
	public Url src;
	
	public List<Document> elements;
	
	public Document (String name) {
		this.name = name;
		this.elements = new ArrayList<Document>();
	}
	
	public Document() {
		
	}

}
