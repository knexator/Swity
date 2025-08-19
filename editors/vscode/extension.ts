import { workspace, ExtensionContext, window } from 'vscode';

import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions
} from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: ExtensionContext) {
	const serverOptions: ServerOptions = {
		run: { command: "swity", args: ["lsp"] },
        debug: { command: "swity", args: ["lsp"] },
	};

	const clientOptions: LanguageClientOptions = {
        documentSelector: [
            { scheme: "file", language: 'swity' },
        ],
		synchronize: {
			fileEvents: workspace.createFileSystemWatcher('**/.swt')
		}
	};

	// Create the language client and start the client.
    const client = new LanguageClient(
      "swity",
      "Swity Language Server",
      serverOptions,
      clientOptions
    );

    client.start().catch(reason => {
        window.showWarningMessage(`Failed to run Swity Language Server: ${reason}`);
    });
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}