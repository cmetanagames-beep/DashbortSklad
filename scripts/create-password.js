const crypto = require('crypto');
const readline = require('readline');

const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
rl.question('Новый пароль: ', password => {
  const salt = crypto.randomBytes(16).toString('hex');
  const passwordHash = crypto.scryptSync(String(password), salt, 64).toString('hex');
  console.log(JSON.stringify({ salt, passwordHash }, null, 2));
  rl.close();
});
