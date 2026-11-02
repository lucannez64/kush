'use strict';

const vscode = require('vscode');
const {
  LanguageClient,
  TransportKind,
} = require('vscode-languageclient/node');

let client;
let outputChannel;

function serverOptions() {
  const configuration = vscode.workspace.getConfiguration('kush');
  const command = configuration.get('server.path', 'kush');
  const args = ['lsp'];
  return {
    run: { command, args, transport: TransportKind.stdio },
    debug: { command, args, transport: TransportKind.stdio },
  };
}

async function stopClient() {
  if (!client) {
    return;
  }
  const current = client;
  client = undefined;
  try {
    await current.stop();
  } catch (error) {
    outputChannel.appendLine(`kush: error while stopping server: ${error}`);
  }
}

async function startClient() {
  const configuration = vscode.workspace.getConfiguration('kush');
  await stopClient();
  if (!configuration.get('server.enabled', true)) {
    return;
  }
  if (!outputChannel) {
    outputChannel = vscode.window.createOutputChannel('Kush Language Server');
  }
  const next = new LanguageClient(
    'kush-lsp',
    'Kush Language Server',
    serverOptions(),
    {
      documentSelector: [{ scheme: 'file', language: 'kush' }],
      synchronize: {
        fileEvents: vscode.workspace.createFileSystemWatcher('**/*.kush'),
      },
      outputChannel,
    },
  );
  client = next;
  try {
    await next.start();
    outputChannel.appendLine('kush: language server started');
  } catch (error) {
    if (client === next) {
      client = undefined;
    }
    outputChannel.appendLine(`kush: cannot start language server: ${error}`);
    const selection = await vscode.window.showErrorMessage(
      `Kush language server failed to start: ${error}. Set "kush.server.path" to the kush executable.`,
      'Open Settings',
    );
    if (selection === 'Open Settings') {
      await vscode.commands.executeCommand(
        'workbench.action.openSettings',
        'kush.server.path',
      );
    }
  }
}

async function activate(context) {
  outputChannel = vscode.window.createOutputChannel('Kush Language Server');
  context.subscriptions.push(outputChannel);
  context.subscriptions.push(
    vscode.commands.registerCommand('kush.restartLanguageServer', async () => {
      await startClient();
    }),
  );
  context.subscriptions.push(
    vscode.workspace.onDidChangeConfiguration(async (event) => {
      if (
        event.affectsConfiguration('kush.server.path') ||
        event.affectsConfiguration('kush.server.enabled')
      ) {
        await startClient();
      }
    }),
  );
  await startClient();
}

async function deactivate() {
  await stopClient();
}

module.exports = { activate, deactivate };
