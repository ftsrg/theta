package hu.bme.mit.inf.ttmc.program.ui;

import java.io.IOException;
import java.util.Collections;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;

import com.google.inject.Inject;
import com.google.inject.Injector;


import hu.bme.mit.inf.ttmc.program.language.ProgramLanguageStandaloneSetup;
import hu.bme.mit.inf.ttmc.program.model.ProgramModelPackage;
import hu.bme.mit.inf.ttmc.program.model.ProgramSpecification;

public class ProgramModelLoader {

	private static ProgramModelLoader instance;

	@Inject
	private XtextResourceSet resourceSet;

	private ProgramModelLoader() {
		final ProgramLanguageStandaloneSetup setup = new ProgramLanguageStandaloneSetup();
		final Injector injector = setup.createInjectorAndDoEMFRegistration();
		ProgramModelPackage.eINSTANCE.eClass();
		injector.injectMembers(this);
		resourceSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);
	}

	public static ProgramModelLoader getInstance() {
		if (instance == null) {
			instance = new ProgramModelLoader();
		}
		return instance;
	}

	public ProgramSpecification load(String filePath) {
		final URI uri = URI.createFileURI(filePath);
		final Resource resource = resourceSet.getResource(uri, true);
		final EObject object = resource.getContents().get(0);
		final ProgramSpecification specification = (ProgramSpecification) object;
		return specification;
	}

	public void save(ProgramSpecification specification, String fileName) throws IOException {
		final URI uri = URI.createFileURI(fileName);
		final Resource resource = resourceSet.createResource(uri);
		resource.getContents().add(specification);
       	resource.save(Collections.EMPTY_MAP);
    }
}
