/**
 * Copyright (c) 2016, 2019 YCSB contributors. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you
 * may not use this file except in compliance with the License. You
 * may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing
 * permissions and limitations under the License. See accompanying
 * LICENSE file.
 */
package site.ycsb.db.flavors;

import site.ycsb.db.JdbcDBClient;
import site.ycsb.db.StatementType;

/**
 * A default flavor for relational databases.
 */
public class PrivacyProxyDBFlavor extends DBFlavor {
//  private static final String schema = "canonical.";
  private static final String schema = "";
  private static final String db = "public.";

  public PrivacyProxyDBFlavor() {
    super(DBName.PRIVACY_PROXY);
  }
  public PrivacyProxyDBFlavor(DBName dbName) {
    super(dbName);
  }

  @Override
  public String createInsertStatement(StatementType insertType, String key) {
    StringBuilder insert = new StringBuilder("INSERT INTO ");
    insert.append(db).append(insertType.getTableName());
    insert.append(" (" + JdbcDBClient.PRIMARY_KEY + "," + insertType.getFieldString() + ")");
    insert.append(" VALUES(?");
    for (int i = 0; i < insertType.getNumFields(); i++) {
      insert.append(",?");
    }
    insert.append(")");
    return insert.toString();
  }

  @Override
  public String createReadStatement(StatementType readType, String key) {
    StringBuilder read = new StringBuilder("SELECT YCSB_KEY, FIELD0, FIELD1, FIELD2, FIELD3, FIELD4, FIELD5, FIELD6, FIELD7, FIELD8, FIELD9 FROM ");
    read.append(schema).append(db).append(readType.getTableName());
    read.append(" WHERE ");
    read.append(JdbcDBClient.PRIMARY_KEY);
    read.append(" = ");
    read.append("?");
    return read.toString();
  }

  @Override
  public String createDeleteStatement(StatementType deleteType, String key) {
    StringBuilder delete = new StringBuilder("DELETE FROM ");
    delete.append(db).append(deleteType.getTableName());
    delete.append(" WHERE ");
    delete.append(JdbcDBClient.PRIMARY_KEY);
    delete.append(" = ?");
    return delete.toString();
  }

  @Override
  public String createUpdateStatement(StatementType updateType, String key) {
    String[] fieldKeys = updateType.getFieldString().split(",");
    StringBuilder update = new StringBuilder("UPDATE ");
    update.append(db).append(updateType.getTableName());
    update.append(" SET ");
    for (int i = 0; i < fieldKeys.length; i++) {
      update.append(fieldKeys[i]);
      update.append("=?");
      if (i < fieldKeys.length - 1) {
        update.append(", ");
      }
    }
    update.append(" WHERE ");
    update.append(JdbcDBClient.PRIMARY_KEY);
    update.append(" = ?");
    return update.toString();
  }

  @Override
  public String createScanStatement(StatementType scanType, String key, boolean sqlserverScans, boolean sqlansiScans) {
    StringBuilder select;
    if (sqlserverScans) {
      select = new StringBuilder("SELECT TOP (?) * FROM ");
    } else {
      select = new StringBuilder("SELECT * FROM ");
    }
    select.append(schema).append(db).append(scanType.getTableName());
    select.append(" WHERE ");
    select.append(JdbcDBClient.PRIMARY_KEY);
    select.append(" >= ?");
    select.append(" ORDER BY ");
    select.append(JdbcDBClient.PRIMARY_KEY);
    if (!sqlserverScans) {
      if (sqlansiScans) {
        select.append(" FETCH FIRST ? ROWS ONLY");
      } else {
        select.append(" LIMIT ?");
      }
    }
    return select.toString();
  }
}
