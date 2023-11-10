package model.url;

public class BlobOnlyDomainUrl extends Url {
	
	public Domain domain;
	
	public BlobOnlyDomainUrl(String name) {
		super(name);
		this.scheme = Scheme.Blob;
		this.corresponding = "example.com";
	}

}
