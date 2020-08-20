/*
 * Copyright (c) 2015. Qubole Inc
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 *    limitations under the License.
 */

package catalog.db;

import com.google.common.collect.ImmutableList;
import sql.PrivacyException;

import catalog.db.dao.JdbcSourceDAO;
import catalog.db.dao.QuboleDbSourceDAO;
import catalog.db.dao.ViewDAO;
import catalog.db.pojo.DSSet;
import catalog.db.pojo.DataSource;
import catalog.db.pojo.JdbcSource;
import catalog.db.pojo.QuboleDbSource;
import catalog.db.pojo.View;

import planner.PrivacyFactory;
import planner.PrivacyFactoryResult;

import org.skife.jdbi.v2.DBI;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

/**
 * Sets up and organizes the planner with tables from all federated data sources.
 * The info argument encodes all the required information (described below) as
 * JSON.
 * Consider an example where there are 3 data sources:
 * <ul>
 * <li>CANONICAL</li>
 * <li>CUBES</li>
 * <li>VIEWS</li>
 * </ul>
 * CANONICAL is the default. Each of the data sources have many schemas and
 * tables. This class and its dependents set up such that the tables can be
 * referred as follows:
 * <ul>
 * <li><i>canonical.default.lineitem</i> refers to a table in DEFAULT in CANONICAL.</li>
 * <li><i>canonical.tpch.customers</i> refers to a table in TPCH in CANONICAL.</li>
 * <li><i>lineitem</i> refers to a table in DEFAULT in CANONICAL.</li>
 * <li><i>CUBES.PUBLIC.WEB_RETURNS</i> refers to a table in PUBLIC in CUBES.</li>
 * </ul>
 *
 */
public class SchemaFactory implements PrivacyFactory {
  private static final Logger LOG = LoggerFactory.getLogger(SchemaFactory.class);

  /**
   * Creates list of QuarkSchema
   *
   * @param info A JSON string which contains database credentials
   * @return
   * @throws PrivacyException
   */
  public PrivacyFactoryResult create(Properties info) throws PrivacyException {
    try {
      Connection connection = new Connection(info);
      connection.runFlyWay();

      DSSet dsSet = connection.getDSSet();
      DBI dbi = connection.getDbi();

      JdbcSourceDAO jdbcSourceDAO = dbi.onDemand(JdbcSourceDAO.class);
      QuboleDbSourceDAO quboleDbSourceDAO = dbi.onDemand(QuboleDbSourceDAO.class);
      ViewDAO viewDAO = dbi.onDemand(ViewDAO.class);

      long dsSetId = dsSet.getId();
      long defaultDataSourceId = dsSet.getDefaultDatasourceId();

      List<JdbcSource> jdbcSources = jdbcSourceDAO.findByDSSetId(dsSetId);
      List<QuboleDbSource> quboleDbSources = quboleDbSourceDAO.findByDSSetId(dsSetId);

      List<DataSource> dataSources = new ArrayList<>();
      dataSources.addAll(jdbcSources);
      dataSources.addAll(quboleDbSources);

      ImmutableList.Builder<planner.DataSourceSchema> schemaList =
          new ImmutableList.Builder<>();

      planner.DataSourceSchema defaultSchema = null;

      for (DataSource dataSource : dataSources) {
        planner.DataSourceSchema dataSourceSchema = new DataSourceSchema(
            dataSource.getProperties(defaultDataSourceId));
        if (dataSource.getId() == defaultDataSourceId) {
          defaultSchema = dataSourceSchema;
        }
        schemaList.add(dataSourceSchema);
      }

      RelSchema relSchema = getRelSchema(viewDAO, dsSetId);

      return new PrivacyFactoryResult(schemaList.build(), relSchema, defaultSchema);
    } catch (Exception se) {
      LOG.error(se.getMessage());
      throw new PrivacyException(se);
    }
  }

  private RelSchema getRelSchema(ViewDAO viewDAO,
                                 long dsSetId) {

    List<View> views = viewDAO.findByDSSetId(dsSetId);
    List<RelSchema.DbView> dbViews = new ArrayList<RelSchema.DbView>();

    for (View view : views) {
      dbViews.add(new RelSchema.DbView(view.getName(), view.getQuery(),
          view.getTable(), view.getSchema(), view.getDestination()));
    }

    return new RelSchema(dbViews);
  }
}
